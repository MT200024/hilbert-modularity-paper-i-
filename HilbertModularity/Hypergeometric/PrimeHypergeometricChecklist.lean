/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.ModularityChecklist
public import HilbertModularity.Hypergeometric.ModularityOrdinaryTransport
public import HilbertModularity.Geometry.GroupScheme.PrimeHypergeometricDeterminant
public import HilbertModularity.Geometry.GroupScheme.PrimeHypergeometricOrdinary
public import HilbertModularity.Hypergeometric.PrimeResidualMatrixComparison

/-! # Skinner–Wiles data for the selected prime plus family

The fixed torsion point and determinant used below belong to the same selected
plus-family fibre. Comparison with a two-dimensional integral lattice remains
an explicit premise. See [DarmonRigid, Theorem 2.6(2)], [DarmonMestre, Section 4]
and [TripathiGoswamiRevised, Proposition `SW-checklist`].
-/

public section
noncomputable section

open scoped NumberField Pointwise ValuativeRel TensorProduct
open scoped IsMulCommutative
open ValuativeRel NumberField AlgebraicGeometry AlgebraicGeometry.GroupScheme
open IsDedekindDomain

namespace HilbertModularity.Hypergeometric

open HilbertModularity.Cyclotomic HilbertModularity.HilbertModularForms
  IsNonarchimedeanLocalField

attribute [local instance] realFieldAlgebra realPrimePowerCompletionPadicAlgebra

local instance primePlusChecklistIntegerQuotientCharP
    (p : ℕ) [Fact p.Prime] :
    CharP (𝒪[RealPrimePowerCompletion p 0] ⧸ 𝓂[RealPrimePowerCompletion p 0]) p :=
  inferInstanceAs (CharP 𝓀[RealPrimePowerCompletion p 0] p)

local instance realPrimeCompletionGalCompact
    (p : ℕ) [Fact p.Prime] :
    CompactSpace (Gal(PadicAlgCl p/RealPrimePowerCompletion p 0)) := by
  let : IsGalois (RealPrimePowerCompletion p 0) (PadicAlgCl p) :=
    IsGalois.tower_top_of_isGalois ℚ_[p]
      (RealPrimePowerCompletion p 0) (PadicAlgCl p)
  infer_instance

/-- The normalized ordinary data of the selected plus Jacobian give the local
Skinner–Wiles condition after restricting the SAME global representation and
identifying the residual characters on its SAME integral lattice. These three
comparisons and inertia containment are explicit inputs; the triangular and
finite-inertia conclusions follow from the actual quotient and
[Caruso2019, Theorem 2.2.1]. See [SkinnerWiles, §4.5, Theorem A]. -/
def PrimePlusNormalizedOrdinaryData.skinnerWilesOrdinaryAt
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (m : ℕ) (hm : m.Coprime (p ^ (0 + 1)))
    (d : PrimePlusNormalizedOrdinaryData p hp ξ m hm)
    (ρ : Representation (RealPrimePowerCompletion p 0)
      (AbsoluteGalois (realCyclotomicField p))
      (Fin 2 → RealPrimePowerCompletion p 0))
    (D : SkinnerWilesResidualData ρ)
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p)))) [Q.IsMaximal]
    (φ : primeDecompositionGroup Q →*
      Gal(PadicAlgCl p/RealPrimePowerCompletion p 0))
    (hφ : Continuous φ)
    (hρ : ∀ g : primeDecompositionGroup Q,
      ρ (g : AbsoluteGalois (realCyclotomicField p)) =
        d.coordinateRepresentation p hp ξ (φ g))
    (hδ₁ : ∀ g : primeDecompositionGroup Q,
      ((Units.map (Ideal.Quotient.mk 𝓂[RealPrimePowerCompletion p 0] :
          𝒪[RealPrimePowerCompletion p 0] →*
            𝒪[RealPrimePowerCompletion p 0] ⧸ 𝓂[RealPrimePowerCompletion p 0])).comp
        (integerCharacter (RealPrimePowerCompletion p 0)
          d.upperCharacter d.upper_continuous)) (φ g) =
        D.chi₁ (g : AbsoluteGalois (realCyclotomicField p)))
    (hδ₂ : ∀ g : primeDecompositionGroup Q,
      ((Units.map (Ideal.Quotient.mk 𝓂[RealPrimePowerCompletion p 0] :
          𝒪[RealPrimePowerCompletion p 0] →*
            𝒪[RealPrimePowerCompletion p 0] ⧸ 𝓂[RealPrimePowerCompletion p 0])).comp
        (Representation.determinantCharacter d.lattice.toRepresentation)) (φ g) =
        D.chi₂ (g : AbsoluteGalois (realCyclotomicField p)))
    (hI : ∀ g : primeDecompositionGroup Q,
      (g : AbsoluteGalois (realCyclotomicField p)) ∈
        Q.inertia (AbsoluteGalois (realCyclotomicField p)) →
        φ g ∈ PadicAlgCl.inertia p (RealPrimePowerCompletion p 0)) :
    SkinnerWilesOrdinaryAt p ρ D Q := by
  letI : IsGalois (RealPrimePowerCompletion p 0) (PadicAlgCl p) :=
    IsGalois.tower_top_of_isGalois ℚ_[p]
      (RealPrimePowerCompletion p 0) (PadicAlgCl p)
  letI := d.lattice_isLattice
  let σ := d.coordinateRepresentation p hp ξ
  have hentry (g : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0))
      (i j : Fin 2) :
      σ g (Pi.single j 1) i =
        LinearMap.toMatrix d.basis d.basis
          ((primePlusDecompositionScalarConjugate p hp ξ m hm).ρ g) i j := by
    dsimp [σ, PrimePlusNormalizedOrdinaryData.coordinateRepresentation]
    change d.basis.equivFun
      ((primePlusDecompositionScalarConjugate p hp ξ m hm).ρ g
        (d.basis.equivFun.symm (Pi.single j 1))) i = _
    simp only [LinearMap.toMatrix_apply]
    simp
  exact skinnerWilesOrdinaryAt_of_characterLattice p ρ D Q σ φ hφ hρ
    (LinearEquiv.refl _ _) d.upperCharacter d.lowerCharacter
    d.upper_continuous d.lower_continuous d.lattice
    ((Units.map (Ideal.Quotient.mk 𝓂[RealPrimePowerCompletion p 0] :
      𝒪[RealPrimePowerCompletion p 0] →*
        𝒪[RealPrimePowerCompletion p 0] ⧸ 𝓂[RealPrimePowerCompletion p 0])).comp
      (integerCharacter (RealPrimePowerCompletion p 0)
        d.upperCharacter d.upper_continuous))
    rfl hδ₁ hδ₂ (PadicAlgCl.inertia p (RealPrimePowerCompletion p 0))
    hI d.finite_normalized_inertia
    (by
      intro g
      change σ g (Pi.single 0 1) 1 = 0
      rw [hentry g 1 0, d.upperTriangular g]
      rfl)
    (by
      intro g
      change σ g (Pi.single 0 1) 0 =
        (d.upperCharacter g : RealPrimePowerCompletion p 0)
      rw [hentry g 0 0, d.upperTriangular g]
      rfl)
    (by
      intro g
      change σ g (Pi.single 1 1) 1 =
        (d.lowerCharacter g : RealPrimePowerCompletion p 0)
      rw [hentry g 1 1, d.upperTriangular g]
      rfl)

/-- An equivariant identification of the chosen global coordinates with the
selected plus Jacobian's local coordinates transports its ordinary basis to
the global action. This retains the actual local intertwiner instead of
requiring the two coordinate actions to be literally equal. -/
def PrimePlusNormalizedOrdinaryData.skinnerWilesOrdinaryAt_of_equiv
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (m : ℕ) (hm : m.Coprime (p ^ (0 + 1)))
    (d : PrimePlusNormalizedOrdinaryData p hp ξ m hm)
    (ρ : Representation (RealPrimePowerCompletion p 0)
      (AbsoluteGalois (realCyclotomicField p))
      (Fin 2 → RealPrimePowerCompletion p 0))
    (D : SkinnerWilesResidualData ρ)
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p)))) [Q.IsMaximal]
    (φ : primeDecompositionGroup Q →*
      Gal(PadicAlgCl p/RealPrimePowerCompletion p 0))
    (hφ : Continuous φ)
    (e : (Fin 2 → RealPrimePowerCompletion p 0) ≃ₗ[RealPrimePowerCompletion p 0]
      (Fin 2 → RealPrimePowerCompletion p 0))
    (hρ : ∀ (g : primeDecompositionGroup Q)
      (v : Fin 2 → RealPrimePowerCompletion p 0),
      e (ρ (g : AbsoluteGalois (realCyclotomicField p)) v) =
        d.coordinateRepresentation p hp ξ (φ g) (e v))
    (hδ₁ : ∀ g : primeDecompositionGroup Q,
      ((Units.map (Ideal.Quotient.mk 𝓂[RealPrimePowerCompletion p 0] :
          𝒪[RealPrimePowerCompletion p 0] →*
            𝒪[RealPrimePowerCompletion p 0] ⧸ 𝓂[RealPrimePowerCompletion p 0])).comp
        (integerCharacter (RealPrimePowerCompletion p 0)
          d.upperCharacter d.upper_continuous)) (φ g) =
        D.chi₁ (g : AbsoluteGalois (realCyclotomicField p)))
    (hδ₂ : ∀ g : primeDecompositionGroup Q,
      ((Units.map (Ideal.Quotient.mk 𝓂[RealPrimePowerCompletion p 0] :
          𝒪[RealPrimePowerCompletion p 0] →*
            𝒪[RealPrimePowerCompletion p 0] ⧸ 𝓂[RealPrimePowerCompletion p 0])).comp
        (Representation.determinantCharacter d.lattice.toRepresentation)) (φ g) =
        D.chi₂ (g : AbsoluteGalois (realCyclotomicField p)))
    (hI : ∀ g : primeDecompositionGroup Q,
      (g : AbsoluteGalois (realCyclotomicField p)) ∈
        Q.inertia (AbsoluteGalois (realCyclotomicField p)) →
        φ g ∈ PadicAlgCl.inertia p (RealPrimePowerCompletion p 0)) :
    SkinnerWilesOrdinaryAt p ρ D Q := by
  let σ := d.coordinateRepresentation p hp ξ
  let τ : Representation (RealPrimePowerCompletion p 0)
      (Gal(PadicAlgCl p/RealPrimePowerCompletion p 0))
      (Fin 2 → RealPrimePowerCompletion p 0) :=
    e.symm.conjRingEquiv.toMonoidHom.comp σ
  have hτ (g : primeDecompositionGroup Q) :
      ρ (g : AbsoluteGalois (realCyclotomicField p)) = τ (φ g) := by
    apply LinearMap.ext
    intro v
    apply e.injective
    change e (ρ (g : AbsoluteGalois (realCyclotomicField p)) v) =
      e (e.symm (σ (φ g) (e v)))
    simpa only [e.apply_symm_apply] using hρ g v
  have hentry (g : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0))
      (i j : Fin 2) :
      e (τ g (e.symm (Pi.single j 1))) i =
        LinearMap.toMatrix d.basis d.basis
          ((primePlusDecompositionScalarConjugate p hp ξ m hm).ρ g) i j := by
    dsimp [τ, σ, PrimePlusNormalizedOrdinaryData.coordinateRepresentation]
    simp only [LinearEquiv.conjRingEquiv_apply_apply,
      LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply,
      LinearMap.toMatrix_apply]
    simp
  letI : IsGalois (RealPrimePowerCompletion p 0) (PadicAlgCl p) :=
    IsGalois.tower_top_of_isGalois ℚ_[p]
      (RealPrimePowerCompletion p 0) (PadicAlgCl p)
  letI := d.lattice_isLattice
  exact skinnerWilesOrdinaryAt_of_characterLattice p ρ D Q τ φ hφ hτ e
    d.upperCharacter d.lowerCharacter d.upper_continuous d.lower_continuous d.lattice
    ((Units.map (Ideal.Quotient.mk 𝓂[RealPrimePowerCompletion p 0] :
      𝒪[RealPrimePowerCompletion p 0] →*
        𝒪[RealPrimePowerCompletion p 0] ⧸ 𝓂[RealPrimePowerCompletion p 0])).comp
      (integerCharacter (RealPrimePowerCompletion p 0)
        d.upperCharacter d.upper_continuous))
    rfl hδ₁ hδ₂ (PadicAlgCl.inertia p (RealPrimePowerCompletion p 0))
    hI d.finite_normalized_inertia
    (by
      intro g
      rw [hentry g 1 0, d.upperTriangular g]
      rfl)
    (by
      intro g
      rw [hentry g 0 0, d.upperTriangular g]
      rfl)
    (by
      intro g
      rw [hentry g 1 1, d.upperTriangular g]
      rfl)

/-- The rational point of the selected plus family determines the residual
character ratio on any specified lattice representing its canonical-prime
kernel. The exact Tate determinant and both lattice comparisons are explicit
arithmetic premises. -/
theorem residualRatio_eq_primePlus_of_kernelComparison
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    {E : Type*} [Field E] [ValuativeRel E]
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E]
    [FaithfulSMul (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E]
    (ρ : Representation E (AbsoluteGalois (realCyclotomicField p)) (Fin 2 → E))
    (D : HilbertModularForms.SkinnerWilesResidualData ρ)
    (κ : (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) ≃+*
      (𝒪[E] ⧸ 𝓂[E]))
    (j : Points (realCyclotomicField p)
        (AlgebraicClosure (realCyclotomicField p))
        (primePlusKernel p hp ξ).X ≃+ (Fin 2 → 𝒪[E] ⧸ 𝓂[E]))
    (hequiv : ∀ (g : AbsoluteGalois (realCyclotomicField p)) v,
      j (g • v) =
        ((LinearMap.toMatrix' (D.integralAction g)).map
          (Ideal.Quotient.mk (𝓂[E]))).mulVec (j v))
    (hTateDet : ∀ g : AbsoluteGalois (realCyclotomicField p),
      letI := primePlusIntegralTateModule p hp ξ
      LinearMap.det ((primePlusIntegralTateRepresentation p hp ξ).baseChange E g) =
        algebraMap (AdicCompletion (Ideal.span {realPrimeGenerator p})
          (𝓞 (realCyclotomicField p))) E
          (TateModule.coefficientPrimeRingEquiv p
            (𝓞 (realCyclotomicField p))
            (Ideal.span {realPrimeGenerator p}) ((p - 1) / 2)
            (realPrimeRamification_pos p (by omega))
            (span_realPrimeGenerator_pow p (by omega))
              (PadicInt.toAdicCompletion p (𝓞 (realCyclotomicField p))
                (Field.cyclotomicCharacter (realCyclotomicField p) p g : ℤ_[p]))))
    (b : letI := primePlusKernelModule p hp ξ
      Module.Basis (Fin 2)
        (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p})
        (Points (realCyclotomicField p)
          (AlgebraicClosure (realCyclotomicField p)) (primePlusKernel p hp ξ).X))
    (hmat : ∀ g : AbsoluteGalois (realCyclotomicField p),
      letI := primePlusKernelModule p hp ξ
      (LinearMap.toMatrix b b
        (primePlusKernelRepresentation p hp ξ g)).map
          κ.toRingHom =
        (LinearMap.toMatrix' (D.integralAction g)).map
          (Ideal.Quotient.mk (𝓂[E]))) :
    HilbertModularForms.residualRatio D =
      (Units.map κ.toMonoidHom).comp
        (AlgebraicGeometry.GroupScheme.realPrimeResidualCyclotomicCharacter
          (realCyclotomicField p) p (by omega)) := by
  let := coefficientKernelModule (realCyclotomicField p)
    (primePlusFiber p hp ξ) (𝓞 (realCyclotomicField p))
      (primePlusFiberRealMultiplication p hp ξ) (realPrimeGenerator p)
  have hdetCompare := residualDeterminant_eq_of_kernelMatrixComparison
    p hp ξ κ ρ D b hmat
  have hkernelDet : ∀ g : AbsoluteGalois (realCyclotomicField p),
      LinearMap.det (coefficientKernelRepresentation
        (realCyclotomicField p) (primePlusFiber p hp ξ)
          (𝓞 (realCyclotomicField p))
            (primePlusFiberRealMultiplication p hp ξ) (realPrimeGenerator p) g) =
        (AlgebraicGeometry.GroupScheme.realPrimeResidualCyclotomicCharacter
          (realCyclotomicField p) p (by omega) g :
            𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) := by
    intro g
    have h := congrArg (fun f => f g)
      (primePlusResidualDeterminantCharacter_of_integralTate p hp ξ E (by
        exact hTateDet))
    exact congrArg Units.val h
  let ε := (Units.map κ.toMonoidHom).comp
    (AlgebraicGeometry.GroupScheme.realPrimeResidualCyclotomicCharacter
      (realCyclotomicField p) p (by omega))
  have hquad : ∀ g, ε g = 1 ∨ ε g = -1 := by
    intro g
    rcases realPrimeResidualCharacter_eq_one_or_neg_one p (by omega) g with h | h
    · left
      simp [ε, h]
    · right
      simp [ε, h]
  obtain ⟨v, hv, hfix⟩ := exists_primePlusKernel_fixed p hp ξ
  let w := j v
  have hw : w ≠ 0 := by
    intro h
    apply hv
    apply j.injective
    simpa [w] using h
  have hwfix : ∀ g : AbsoluteGalois (realCyclotomicField p),
      ((LinearMap.toMatrix' (D.integralAction g)).map
        (Ideal.Quotient.mk (𝓂[E]))).mulVec w = w := by
    intro g
    calc
      _ = j (g • v) := (hequiv g v).symm
      _ = w := by rw [hfix g]
  have hdet : ∀ g : AbsoluteGalois (realCyclotomicField p),
      Ideal.Quotient.mk (𝓂[E]) (LinearMap.det (D.integralAction g)) =
        (ε g : 𝒪[E] ⧸ 𝓂[E]) := by
    intro g
    calc
      _ = κ (LinearMap.det (coefficientKernelRepresentation
          (realCyclotomicField p) (primePlusFiber p hp ξ)
            (𝓞 (realCyclotomicField p))
              (primePlusFiberRealMultiplication p hp ξ) (realPrimeGenerator p) g)) :=
        (by simpa only [det_primePlusKernelRepresentation] using hdetCompare g)
      _ = κ (AlgebraicGeometry.GroupScheme.realPrimeResidualCyclotomicCharacter
          (realCyclotomicField p) p (by omega) g :
            𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) := by
        rw [hkernelDet g]
      _ = (ε g : 𝒪[E] ⧸ 𝓂[E]) := (rfl)
  exact residualRatio_eq_quadratic_of_fixed_reduction ρ D ε hquad w hw hwfix hdet

/-- The selected plus Jacobian's residual Tate basis supplies the kernel
coordinates used by the residual Skinner–Wiles argument. The remaining
arithmetic input compares the reduction of the *same integral Tate action*
with the chosen integral two-dimensional action, entry by entry. No separate
kernel identification or equivariance premise is needed. -/
theorem residualRatio_eq_primePlus_of_residualTateMatrix
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    {E : Type*} [Field E] [ValuativeRel E]
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E]
    [FaithfulSMul (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E]
    (ρ : Representation E (AbsoluteGalois (realCyclotomicField p)) (Fin 2 → E))
    (D : HilbertModularForms.SkinnerWilesResidualData ρ)
    (κ : (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) ≃+*
      (𝒪[E] ⧸ 𝓂[E]))
    (hTateDet : ∀ g : AbsoluteGalois (realCyclotomicField p),
      letI := primePlusIntegralTateModule p hp ξ
      LinearMap.det ((primePlusIntegralTateRepresentation p hp ξ).baseChange E g) =
        algebraMap (AdicCompletion (Ideal.span {realPrimeGenerator p})
          (𝓞 (realCyclotomicField p))) E
          (TateModule.coefficientPrimeRingEquiv p
            (𝓞 (realCyclotomicField p))
            (Ideal.span {realPrimeGenerator p}) ((p - 1) / 2)
            (realPrimeRamification_pos p (by omega))
            (span_realPrimeGenerator_pow p (by omega))
              (PadicInt.toAdicCompletion p (𝓞 (realCyclotomicField p))
                (Field.cyclotomicCharacter (realCyclotomicField p) p g : ℤ_[p]))))
    (bRes : letI := primePlusIntegralTateModule p hp ξ
      letI := (AdicCompletion.evalOneₐ
        (Ideal.span {realPrimeGenerator p}) : _).toRingHom.toAlgebra
      Module.Basis (Fin 2)
        (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p})
        ((𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) ⊗[AdicCompletion
          (Ideal.span {realPrimeGenerator p}) (𝓞 (realCyclotomicField p))]
          (integralTate (realCyclotomicField p) (primePlusFiber p hp ξ).X p)))
    (hres : ∀ g : AbsoluteGalois (realCyclotomicField p),
      letI := primePlusIntegralTateModule p hp ξ
      letI := (AdicCompletion.evalOneₐ
        (Ideal.span {realPrimeGenerator p}) : _).toRingHom.toAlgebra
      (LinearMap.toMatrix bRes bRes
        ((primePlusIntegralTateRepresentation p hp ξ).baseChange
          (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) g)).map
            κ.toRingHom =
        (LinearMap.toMatrix' (D.integralAction g)).map
          (Ideal.Quotient.mk (𝓂[E]))) :
    HilbertModularForms.residualRatio D =
      (Units.map κ.toMonoidHom).comp
        (AlgebraicGeometry.GroupScheme.realPrimeResidualCyclotomicCharacter
          (realCyclotomicField p) p (by omega)) := by
  let := primePlusIntegralTateModule p hp ξ
  let := primePlusKernelModule p hp ξ
  let := (AdicCompletion.evalOneₐ
    (Ideal.span {realPrimeGenerator p}) : _).toRingHom.toAlgebra
  let b := primePlusKernelBasisOfResidualTate p hp ξ bRes
  let j := primePlusKernelCoordinateEquiv p hp ξ κ b
  have hmat : ∀ g : AbsoluteGalois (realCyclotomicField p),
      (LinearMap.toMatrix b b (primePlusKernelRepresentation p hp ξ g)).map
        κ.toRingHom =
        (LinearMap.toMatrix' (D.integralAction g)).map
          (Ideal.Quotient.mk (𝓂[E])) := by
    intro g
    rw [show LinearMap.toMatrix b b (primePlusKernelRepresentation p hp ξ g) =
        LinearMap.toMatrix bRes bRes
          ((primePlusIntegralTateRepresentation p hp ξ).baseChange
            (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) g) from
      primePlusKernelMatrix_eq_residualTateMatrix p hp ξ bRes g]
    exact hres g
  have hequiv (g : AbsoluteGalois (realCyclotomicField p)) v :
      j (g • v) =
        ((LinearMap.toMatrix' (D.integralAction g)).map
          (Ideal.Quotient.mk (𝓂[E]))).mulVec (j v) :=
    primePlusKernelCoordinateEquiv_galois p hp ξ ρ D κ b hmat g v
  exact residualRatio_eq_primePlus_of_kernelComparison p hp ξ ρ D κ j
    hequiv hTateDet b hmat

/-- The residual ratio calculation in the coordinates obtained from an
integral basis of the selected plus Jacobian's Tate lattice. The matrix
comparison with the chosen Skinner–Wiles integral action remains explicit. -/
theorem residualRatio_eq_primePlus_of_integralTateMatrix
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    {E : Type*} [Field E] [ValuativeRel E]
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E]
    [FaithfulSMul (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E]
    (ρ : Representation E (AbsoluteGalois (realCyclotomicField p)) (Fin 2 → E))
    (D : HilbertModularForms.SkinnerWilesResidualData ρ)
    (κ : (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) ≃+*
      (𝒪[E] ⧸ 𝓂[E]))
    (hTateDet : ∀ g : AbsoluteGalois (realCyclotomicField p),
      letI := primePlusIntegralTateModule p hp ξ
      LinearMap.det ((primePlusIntegralTateRepresentation p hp ξ).baseChange E g) =
        algebraMap (AdicCompletion (Ideal.span {realPrimeGenerator p})
          (𝓞 (realCyclotomicField p))) E
          (TateModule.coefficientPrimeRingEquiv p
            (𝓞 (realCyclotomicField p))
            (Ideal.span {realPrimeGenerator p}) ((p - 1) / 2)
            (realPrimeRamification_pos p (by omega))
            (span_realPrimeGenerator_pow p (by omega))
              (PadicInt.toAdicCompletion p (𝓞 (realCyclotomicField p))
                (Field.cyclotomicCharacter (realCyclotomicField p) p g : ℤ_[p]))))
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
          (Ideal.Quotient.mk (𝓂[E]))) :
    HilbertModularForms.residualRatio D =
      (Units.map κ.toMonoidHom).comp
        (AlgebraicGeometry.GroupScheme.realPrimeResidualCyclotomicCharacter
          (realCyclotomicField p) p (by omega)) :=
  residualRatio_eq_primePlus_of_residualTateMatrix p hp ξ ρ D κ hTateDet
    (primePlusResidualTateBasis p hp ξ) hres

/-- On the selected Jacobian's chosen integral Tate coordinates, the
Skinner–Wiles residual matrix comparison follows from the canonical-prime
residue uniqueness. This retains the actual
integral action and its coefficient embedding as arithmetic data; see
[TripathiGoswamiRevised, Proposition `primeresidual` and Proposition
`SW-checklist`]. -/
theorem residualRatio_eq_primePlus_of_integralCoordinateAction
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    {E : Type*} [Field E] [ValuativeRel E]
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E]
    [FaithfulSMul (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E]
    (ρ : Representation E (AbsoluteGalois (realCyclotomicField p)) (Fin 2 → E))
    (D : HilbertModularForms.SkinnerWilesResidualData ρ)
    (β : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[E])
    (κ : (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) ≃+*
      (𝒪[E] ⧸ 𝓂[E]))
    (hAction : ∀ g : AbsoluteGalois (realCyclotomicField p),
      letI := primePlusIntegralTateModule p hp ξ
      letI : Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
        (𝓞 (realCyclotomicField p))) (𝒪[E]) := β.toAlgebra
      D.integralAction g =
        (((primePlusIntegralTateBasis p hp ξ).baseChange (𝒪[E])).equivFun.conjRingEquiv
          ((primePlusIntegralTateRepresentation p hp ξ).baseChange (𝒪[E]) g)))
    (hTateDet : ∀ g : AbsoluteGalois (realCyclotomicField p),
      letI := primePlusIntegralTateModule p hp ξ
      LinearMap.det ((primePlusIntegralTateRepresentation p hp ξ).baseChange E g) =
        algebraMap (AdicCompletion (Ideal.span {realPrimeGenerator p})
          (𝓞 (realCyclotomicField p))) E
          (TateModule.coefficientPrimeRingEquiv p
            (𝓞 (realCyclotomicField p))
            (Ideal.span {realPrimeGenerator p}) ((p - 1) / 2)
            (realPrimeRamification_pos p (by omega))
            (span_realPrimeGenerator_pow p (by omega))
              (PadicInt.toAdicCompletion p (𝓞 (realCyclotomicField p))
                (Field.cyclotomicCharacter (realCyclotomicField p) p g : ℤ_[p])))) :
    HilbertModularForms.residualRatio D =
      (Units.map κ.toMonoidHom).comp
        (AlgebraicGeometry.GroupScheme.realPrimeResidualCyclotomicCharacter
          (realCyclotomicField p) p (by omega)) := by
  let := primePlusIntegralTateModule p hp ξ
  let := (AdicCompletion.evalOneₐ
    (Ideal.span {realPrimeGenerator p}) : _).toRingHom.toAlgebra
  exact residualRatio_eq_primePlus_of_residualTateMatrix
    p hp ξ ρ D κ hTateDet
    ((primePlusIntegralTateBasis p hp ξ).baseChange
      (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}))
    (fun g => by
      simpa only [hAction g] using
        (primePlusIntegralCoordinateAction_residualMatrix
          p hp ξ β κ g).symm)

/-- The rational canonical-prime torsion point remains fixed in the residual
coordinates of any integral action whose entire matrix is identified with the
selected plus Jacobian's kernel action. -/
theorem exists_primePlusKernel_fixed_in_residualCoordinates
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    {E : Type*} [Field E] [ValuativeRel E]
    (integralAction : Representation (𝒪[E])
      (AbsoluteGalois (realCyclotomicField p)) (Fin 2 → 𝒪[E]))
    (κ : (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) ≃+*
      (𝒪[E] ⧸ 𝓂[E]))
    (b : letI := primePlusKernelModule p hp ξ
      Module.Basis (Fin 2)
        (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p})
        (Points (realCyclotomicField p)
          (AlgebraicClosure (realCyclotomicField p)) (primePlusKernel p hp ξ).X))
    (hmat : ∀ g : AbsoluteGalois (realCyclotomicField p),
      letI := primePlusKernelModule p hp ξ
      (LinearMap.toMatrix b b
        (primePlusKernelRepresentation p hp ξ g)).map κ.toRingHom =
      (LinearMap.toMatrix' (integralAction g)).map
        (Ideal.Quotient.mk (𝓂[E]))) :
    ∃ w : Fin 2 → 𝒪[E] ⧸ 𝓂[E], w ≠ 0 ∧
      ∀ g : AbsoluteGalois (realCyclotomicField p),
        ((LinearMap.toMatrix' (integralAction g)).map
          (Ideal.Quotient.mk (𝓂[E]))).mulVec w = w := by
  let j := primePlusKernelCoordinateEquiv p hp ξ κ b
  obtain ⟨v, hv, hfixed⟩ := exists_primePlusKernel_fixed p hp ξ
  refine ⟨j v, ?_, ?_⟩
  · intro h
    exact hv (j.injective (by simpa only [map_zero] using h))
  · intro g
    rw [← primePlusKernelCoordinateEquiv_galois_for_action p hp ξ
      integralAction κ b hmat g v, hfixed g]

/-- Assemble the weight-two lifting input for the selected prime plus-family Tate
factor. The equivariance, arithmetic residual lattice, ordinary quotients,
ramification and completed-coefficient compatibility are separate premises;
the ratio field, oddness, local distinguishedness and finite-order determinant
are deduced here. See [TripathiGoswamiRevised, Proposition
`SW-checklist`] and [SkinnerWiles, §4.5, Theorem A]. -/
noncomputable def skinnerWilesWeightTwoInput_of_primePlusTateEquiv
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (E : Type*) [NormedField E] [ValuativeRel E]
    [Algebra ℚ_[p] E] [ContinuousSMul ℚ_[p] E]
    [UniformSpace E] [IsUniformAddGroup E] [IsNonarchimedeanLocalField E]
    [CharP (𝒪[E] ⧸ 𝓂[E]) p]
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E]
    [FaithfulSMul (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E]
    (ρ : Representation E (AbsoluteGalois (realCyclotomicField p)) (Fin 2 → E))
    (e : letI := primePlusIntegralTateModule p hp ξ
      ρ.Equiv ((primePlusIntegralTateRepresentation p hp ξ).baseChange E))
    (hTateDet : ∀ g : AbsoluteGalois (realCyclotomicField p),
      letI := primePlusIntegralTateModule p hp ξ
      LinearMap.det ((primePlusIntegralTateRepresentation p hp ξ).baseChange E g) =
        algebraMap (AdicCompletion (Ideal.span {realPrimeGenerator p})
          (𝓞 (realCyclotomicField p))) E
          (TateModule.coefficientPrimeRingEquiv p
            (𝓞 (realCyclotomicField p))
            (Ideal.span {realPrimeGenerator p}) ((p - 1) / 2)
            (realPrimeRamification_pos p (by omega))
            (span_realPrimeGenerator_pow p (by omega))
              (PadicInt.toAdicCompletion p (𝓞 (realCyclotomicField p))
                (Field.cyclotomicCharacter (realCyclotomicField p) p g : ℤ_[p]))))
    (hcoeff : ∀ z : ℤ_[p],
      algebraMap (AdicCompletion (Ideal.span {realPrimeGenerator p})
        (𝓞 (realCyclotomicField p))) E
        (TateModule.coefficientPrimeRingEquiv p
          (𝓞 (realCyclotomicField p))
          (Ideal.span {realPrimeGenerator p}) ((p - 1) / 2)
          (realPrimeRamification_pos p (by omega))
          (span_realPrimeGenerator_pow p (by omega))
            (PadicInt.toAdicCompletion p (𝓞 (realCyclotomicField p)) z)) =
        algebraMap ℚ_[p] E (z : ℚ_[p]))
    (hreal : NumberField.IsTotallyReal (realCyclotomicField p))
    (hcontinuous : ∀ i j : Fin 2,
      Continuous (fun g : AbsoluteGalois (realCyclotomicField p) =>
        ρ g (Pi.single j 1) i))
    (hirred : (Representation.baseChange (AlgebraicClosure E) ρ).IsIrreducible)
    (ramified : Set (HeightOneSpectrum (𝓞 (realCyclotomicField p))))
    (hramified : ramified.Finite)
    (hunramified : ∀ q, q ∉ ramified →
      ∀ (P : Ideal (𝓞 (realCyclotomicField p))) [P.IsMaximal], P = q.asIdeal →
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p))))
        [Q.IsMaximal] [Q.LiesOver P],
      ∀ g : AbsoluteGalois (realCyclotomicField p),
        g ∈ Q.inertia (AbsoluteGalois (realCyclotomicField p)) → ρ g = 1)
    (D : HilbertModularForms.SkinnerWilesResidualData ρ)
    (κ : (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) ≃+*
      (𝒪[E] ⧸ 𝓂[E]))
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
          (Ideal.Quotient.mk (𝓂[E])))
    (hordinary : ∀ (P : Ideal (𝓞 (realCyclotomicField p))) [P.IsMaximal],
      (p : 𝓞 (realCyclotomicField p)) ∈ P →
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p))))
        [Q.IsMaximal] [Q.LiesOver P],
      HilbertModularForms.SkinnerWilesOrdinaryAt p ρ D Q) :
    HilbertModularForms.SkinnerWilesWeightTwoInput p ρ (cyclotomicField p) := by
  have hchar : ∀ g : AbsoluteGalois (realCyclotomicField p),
      HilbertModularForms.residualRatio D g =
        Units.map κ.toMonoidHom
          (AlgebraicGeometry.GroupScheme.realPrimeResidualCyclotomicCharacter
            (realCyclotomicField p) p (by omega) g) := by
    intro g
    exact congrArg (fun f => f g)
      (residualRatio_eq_primePlus_of_integralTateMatrix
        p hp ξ ρ D κ hTateDet hres)
  have hdet : ∀ g : AbsoluteGalois (realCyclotomicField p),
      LinearMap.det (ρ g) =
        (Field.cyclotomicCharacterWithCoefficients
          (realCyclotomicField p) p E g : E) := by
    let : Module
        (AdicCompletion (Ideal.span {realPrimeGenerator p})
          (𝓞 (realCyclotomicField p)))
        (AlgebraicGeometry.GroupScheme.integralTate
          (realCyclotomicField p) (primePlusFiber p hp ξ).X p) :=
      primePlusIntegralTateModule p hp ξ
    intro g
    calc
      LinearMap.det (ρ g) =
          LinearMap.det ((primePlusIntegralTateRepresentation p hp ξ).baseChange E g) :=
        (e.det_eq g).symm
      _ = _ := hTateDet g
      _ = algebraMap ℚ_[p] E
          ((Field.cyclotomicCharacter (realCyclotomicField p) p g : ℤ_[p]) : ℚ_[p]) :=
        hcoeff _
      _ = _ := (Field.cyclotomicCharacterWithCoefficients_coe
        (realCyclotomicField p) p E g).symm
  haveI : IsAbelianGalois ℚ (realCyclotomicField p) :=
    realCyclotomicField_isAbelianGalois p
  refine
    { p_odd := ?_
      totally_real := hreal
      galois_over_rat := inferInstance
      abelian_over_rat := fun σ τ => mul_comm σ τ
      continuous := hcontinuous
      absolutely_irreducible := hirred
      ramified := ramified
      ramified_finite := hramified
      unramified := hunramified
      residual := D
      ratio_field := skinnerWilesRatioField_of_chosenPrime p (by omega) ρ D κ hchar
      ratio_odd := skinnerWilesRatio_odd_of_chosenPrime p (by omega) ρ D κ hchar
      local_ordinary := hordinary
      ratio_distinguished := ?_
      finite_det_character := 1
      finite_det_range := by
        apply (Set.finite_singleton (1 : Eˣ)).subset
        rintro x ⟨g, rfl⟩
        simp
      determinant := ?_ }
  · exact (Fact.out : p.Prime).odd_of_ne_two (by omega)
  · intro P _ hpP Q _ _
    exact skinnerWilesRatio_distinguished_at_prime
      p (by omega) ρ D κ hchar P hpP Q
  · intro g
    simpa using hdet g

end HilbertModularity.Hypergeometric
