/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.PrimeHypergeometricOrdinary

/-! # A Raynaud period map on the selected plus Jacobian

The p-adic Raynaud uniformization supplies a period quotient of the covariant
Tate representation. This module proves the selected Jacobian's ordinary
deduction from an actual surjective RM-linear period map with trivial local
Galois action. Constructing that map from a stable model and the uniformization
is a separate cited geometric input.
-/

public noncomputable section

namespace HilbertModularity.Hypergeometric

open HilbertModularity.Cyclotomic AlgebraicGeometry

attribute [local instance] realPrimePowerCompletionPadicAlgebra
  realPrimePowerCompletionPadicTower realPrimePowerCompletion_uniformContinuousConstSMul
  realPrimePowerCompletionComplexTower
  primePlusDecompositionRationalModule primePlusDecompositionScalarTower
  primePlusConjugateRationalModule primePlusConjugateScalarTower

variable (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
  (ξ : ProjectiveLine.Parameter (realCyclotomicField p))

/-- The kernel of an RM-linear period map is the toric Tate subrepresentation
when the map is locally Galois invariant. The map's source is the completed
covariant Tate module of the actual selected plus Jacobian. -/
def primePlusRaynaudPeriodKernel
    (Y : Type*) [AddCommGroup Y] [Module (RealPrimePowerCompletion p 0) Y]
    (q : primePlusDecompositionRepresentation p hp ξ →ₗ[RealPrimePowerCompletion p 0] Y)
    (hfixed : ∀ (g : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0))
      (v : primePlusDecompositionRepresentation p hp ξ),
      q ((primePlusDecompositionRepresentation p hp ξ).ρ g v) = q v) :
    Subrepresentation (primePlusDecompositionRepresentation p hp ξ).ρ where
  toSubmodule := LinearMap.ker q
  apply_mem_toSubmodule := by
    intro g v hv
    change q ((primePlusDecompositionRepresentation p hp ξ).ρ g v) = 0
    rw [hfixed g v]
    exact hv

/-- The quotient by the kernel of a fixed period map has trivial local
Galois action. Surjectivity and rank are not needed for this assertion. -/
theorem primePlusRaynaudPeriodKernel_quotient_fixed
    (Y : Type*) [AddCommGroup Y] [Module (RealPrimePowerCompletion p 0) Y]
    (q : primePlusDecompositionRepresentation p hp ξ →ₗ[RealPrimePowerCompletion p 0] Y)
    (hfixed : ∀ (g : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0))
      (v : primePlusDecompositionRepresentation p hp ξ),
      q ((primePlusDecompositionRepresentation p hp ξ).ρ g v) = q v)
    (g : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0))
    (v : primePlusDecompositionRepresentation p hp ξ ⧸
      (primePlusRaynaudPeriodKernel p hp ξ Y q hfixed).toSubmodule) :
    (primePlusDecompositionRepresentation p hp ξ).ρ.quotient
      (primePlusRaynaudPeriodKernel p hp ξ Y q hfixed).toSubmodule
      (primePlusRaynaudPeriodKernel p hp ξ Y q hfixed).apply_mem_toSubmodule g v = v := by
  let V := primePlusDecompositionRepresentation p hp ξ
  let S := primePlusRaynaudPeriodKernel p hp ξ Y q hfixed
  induction v using Submodule.Quotient.induction_on with
  | _ w =>
    change (LinearMap.ker q).mkQ (V.ρ g w) = (LinearMap.ker q).mkQ w
    apply q.quotKerEquivRange.injective
    exact Subtype.ext (hfixed g w)

/-- An actual surjective period map with RM action and fixed periods gives
every labelled ordinary quotient of the selected plus Jacobian. Raynaud's
uniformization [RaynaudRigid, §1 Theorem 1 p. 474 and §3(a)--(b) p. 475]
motivates the map, its rank and split-torus Galois action. Their construction
from the stable model is not asserted here. The quotient rank and Hodge--Tate
weight-zero property are proved from the displayed map. -/
theorem nonempty_primePlusOrdinaryQuotient_of_RaynaudPeriodMap
    (Y : Type*) [AddCommGroup Y] [Module (RealPrimePowerCompletion p 0) Y]
    [Module ℚ_[p] Y]
    [IsScalarTower ℚ_[p] (RealPrimePowerCompletion p 0) Y]
    [Module.Finite ℚ_[p] Y]
    (q : primePlusDecompositionRepresentation p hp ξ →ₗ[RealPrimePowerCompletion p 0] Y)
    (hq : Function.Surjective q)
    (hrank : Module.finrank ℚ_[p] Y = (p - 1) / 2)
    (hfixed : ∀ (g : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0))
      (v : primePlusDecompositionRepresentation p hp ξ),
      q ((primePlusDecompositionRepresentation p hp ξ).ρ g v) = q v)
    (m : ℕ) (hm : m.Coprime (p ^ (0 + 1))) :
    Nonempty (PrimePlusOrdinaryQuotient p hp ξ m hm) := by
  let V := primePlusDecompositionRepresentation p hp ξ
  let S := primePlusRaynaudPeriodKernel p hp ξ Y q hfixed
  have hperiod : Module.finrank ℚ_[p] (V ⧸ S.toSubmodule) = (p - 1) / 2 := by
    have e : (V ⧸ S.toSubmodule) ≃ₗ[RealPrimePowerCompletion p 0] Y :=
      q.quotKerEquivOfSurjective hq
    exact (e.restrictScalars ℚ_[p]).finrank_eq.trans hrank
  have htrivial (g : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0))
      (v : V ⧸ S.toSubmodule) :
      V.ρ.quotient S.toSubmodule S.apply_mem_toSubmodule g v = v := by
    exact primePlusRaynaudPeriodKernel_quotient_fixed p hp ξ Y q hfixed g v
  exact nonempty_primePlusOrdinaryQuotient_of_trivialPeriodAction p hp ξ S
    hperiod htrivial m hm

/-- The period-map construction can retain the particular ordinary quotient,
whose Galois action is trivial. This stronger witness keeps the source kernel
available for a subsequent lower-character and residual-lattice comparison. -/
theorem exists_primePlusOrdinaryQuotient_of_RaynaudPeriodMap_with_fixed
    (Y : Type*) [AddCommGroup Y] [Module (RealPrimePowerCompletion p 0) Y]
    [Module ℚ_[p] Y]
    [IsScalarTower ℚ_[p] (RealPrimePowerCompletion p 0) Y]
    [Module.Finite ℚ_[p] Y]
    (q : primePlusDecompositionRepresentation p hp ξ →ₗ[RealPrimePowerCompletion p 0] Y)
    (hq : Function.Surjective q)
    (hrank : Module.finrank ℚ_[p] Y = (p - 1) / 2)
    (hfixed : ∀ (g : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0))
      (v : primePlusDecompositionRepresentation p hp ξ),
      q ((primePlusDecompositionRepresentation p hp ξ).ρ g v) = q v)
    (m : ℕ) (hm : m.Coprime (p ^ (0 + 1))) :
    ∃ W : PrimePlusOrdinaryQuotient p hp ξ m hm,
      ∀ (g : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0))
        (v : (primePlusDecompositionScalarConjugate p hp ξ m hm) ⧸
          W.kernel.toSubmodule),
        (primePlusDecompositionScalarConjugate p hp ξ m hm).ρ.quotient
          W.kernel.toSubmodule W.kernel.apply_mem_toSubmodule g v = v := by
  let V := primePlusDecompositionRepresentation p hp ξ
  let S := primePlusRaynaudPeriodKernel p hp ξ Y q hfixed
  have hperiod : Module.finrank ℚ_[p] (V ⧸ S.toSubmodule) = (p - 1) / 2 := by
    have e : (V ⧸ S.toSubmodule) ≃ₗ[RealPrimePowerCompletion p 0] Y :=
      q.quotKerEquivOfSurjective hq
    exact (e.restrictScalars ℚ_[p]).finrank_eq.trans hrank
  have htrivial (g : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0))
      (v : V ⧸ S.toSubmodule) :
      V.ρ.quotient S.toSubmodule S.apply_mem_toSubmodule g v = v :=
    primePlusRaynaudPeriodKernel_quotient_fixed p hp ξ Y q hfixed g v
  exact exists_primePlusOrdinaryQuotient_of_trivialPeriodAction_with_fixed
    p hp ξ S hperiod htrivial m hm

/-- The native base-label quotient retains the specified period-map kernel
and its trivial Galois action before any coefficient conjugation. -/
theorem exists_primePlusBaseOrdinaryQuotient_of_RaynaudPeriodMap
    (Y : Type*) [AddCommGroup Y] [Module (RealPrimePowerCompletion p 0) Y]
    [Module ℚ_[p] Y]
    [IsScalarTower ℚ_[p] (RealPrimePowerCompletion p 0) Y]
    [Module.Finite ℚ_[p] Y]
    (q : primePlusDecompositionRepresentation p hp ξ →ₗ[RealPrimePowerCompletion p 0] Y)
    (hq : Function.Surjective q)
    (hrank : Module.finrank ℚ_[p] Y = (p - 1) / 2)
    (hfixed : ∀ (g : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0))
      (v : primePlusDecompositionRepresentation p hp ξ),
      q ((primePlusDecompositionRepresentation p hp ξ).ρ g v) = q v) :
    ∃ W : HodgeTate.WeightZeroQuotient p
        (realPrimePowerLocalPeriodAction p 0)
        (realPrimePowerLocalPeriodAction_fixes p 0)
        (primePlusDecompositionRepresentation p hp ξ).ρ,
      ∀ (g : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0))
        (v : (primePlusDecompositionRepresentation p hp ξ) ⧸
          W.kernel.toSubmodule),
        (primePlusDecompositionRepresentation p hp ξ).ρ.quotient
          W.kernel.toSubmodule W.kernel.apply_mem_toSubmodule g v = v := by
  let V := primePlusDecompositionRepresentation p hp ξ
  let S := primePlusRaynaudPeriodKernel p hp ξ Y q hfixed
  have hperiod : Module.finrank ℚ_[p] (V ⧸ S.toSubmodule) = (p - 1) / 2 := by
    have e : (V ⧸ S.toSubmodule) ≃ₗ[RealPrimePowerCompletion p 0] Y :=
      q.quotKerEquivOfSurjective hq
    exact (e.restrictScalars ℚ_[p]).finrank_eq.trans hrank
  have htrivial (g : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0))
      (v : V ⧸ S.toSubmodule) :
      V.ρ.quotient S.toSubmodule S.apply_mem_toSubmodule g v = v :=
    primePlusRaynaudPeriodKernel_quotient_fixed p hp ξ Y q hfixed g v
  obtain ⟨W, hW⟩ := exists_primePlusBaseOrdinaryQuotient_of_trivialPeriodAction
    p hp ξ S hperiod htrivial
  refine ⟨W, ?_⟩
  rw [hW]
  exact htrivial

/-- A one-dimensional character realization of the selected Jacobian's
Raynaud period quotient is the trivial character. This fixes the lower
ordinary character at the local place once the quotient equivalence is
identified on the actual Tate representation. -/
theorem primePlusRaynaudPeriod_quotientCharacter_eq_one
    (Y : Type*) [AddCommGroup Y] [Module (RealPrimePowerCompletion p 0) Y]
    (q : primePlusDecompositionRepresentation p hp ξ →ₗ[RealPrimePowerCompletion p 0] Y)
    (hfixed : ∀ (g : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0))
      (v : primePlusDecompositionRepresentation p hp ξ),
      q ((primePlusDecompositionRepresentation p hp ξ).ρ g v) = q v)
    (χ : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0) →*
      (RealPrimePowerCompletion p 0)ˣ)
    (e : (((primePlusDecompositionRepresentation p hp ξ).ρ.quotient
      (primePlusRaynaudPeriodKernel p hp ξ Y q hfixed).toSubmodule
      (primePlusRaynaudPeriodKernel p hp ξ Y q hfixed).apply_mem_toSubmodule)).Equiv
        (Representation.ofCharacter χ)) :
    χ = 1 := by
  apply MonoidHom.ext
  intro g
  apply Units.ext
  change (χ g : RealPrimePowerCompletion p 0) = 1
  have h := LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' g)
    (e.symm (1 : RealPrimePowerCompletion p 0))
  change e (((primePlusDecompositionRepresentation p hp ξ).ρ.quotient
      (primePlusRaynaudPeriodKernel p hp ξ Y q hfixed).toSubmodule
      (primePlusRaynaudPeriodKernel p hp ξ Y q hfixed).apply_mem_toSubmodule) g
        (e.symm (1 : RealPrimePowerCompletion p 0))) =
    (Representation.ofCharacter χ) g
      (e (e.symm (1 : RealPrimePowerCompletion p 0))) at h
  rw [primePlusRaynaudPeriodKernel_quotient_fixed p hp ξ Y q hfixed g] at h
  simpa only [Representation.ofCharacter_apply, e.apply_symm_apply, mul_one]
    using h.symm

/-- In Raynaud's split toric case, the nondegenerate valuation pairing makes
the period-lattice action trivial: its other argument is the cocharacter
lattice of a split torus. The equivariant RM-linear period map then gives the
ordinary quotient on the same selected Jacobian. The pairing and map are
geometric inputs from [RaynaudRigid, §1 Theorem 1 p. 474 and §3(a)--(b)
p. 475]; this theorem proves their application and does not assert their
existence for the selected stable model. -/
theorem nonempty_primePlusOrdinaryQuotient_of_RaynaudSplitPairing
    (Y : Type*) [AddCommGroup Y] [Module (RealPrimePowerCompletion p 0) Y]
    [Module ℚ_[p] Y]
    [IsScalarTower ℚ_[p] (RealPrimePowerCompletion p 0) Y]
    [Module.Finite ℚ_[p] Y]
    (q : primePlusDecompositionRepresentation p hp ξ →ₗ[RealPrimePowerCompletion p 0] Y)
    (hq : Function.Surjective q)
    (hrank : Module.finrank ℚ_[p] Y = (p - 1) / 2)
    (ρY : Representation ℚ_[p]
      Gal(PadicAlgCl p/RealPrimePowerCompletion p 0) Y)
    (hintertwine : ∀ (g : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0))
      (v : primePlusDecompositionRepresentation p hp ξ),
      q ((primePlusDecompositionRepresentation p hp ξ).ρ g v) = ρY g (q v))
    (X : Type*) [AddCommGroup X] [Module ℚ_[p] X]
    (ρX : Representation ℚ_[p]
      Gal(PadicAlgCl p/RealPrimePowerCompletion p 0) X)
    (hsplit : ∀ g x, ρX g x = x)
    (pairing : Y →ₗ[ℚ_[p]] X →ₗ[ℚ_[p]] ℚ_[p])
    (hnondegenerate : Function.Injective pairing)
    (hequivariant : ∀ g y x,
      pairing (ρY g y) (ρX g x) = pairing y x)
    (m : ℕ) (hm : m.Coprime (p ^ (0 + 1))) :
    Nonempty (PrimePlusOrdinaryQuotient p hp ξ m hm) := by
  have hperiodFixed (g : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0))
      (y : Y) : ρY g y = y := by
    apply hnondegenerate
    apply LinearMap.ext
    intro x
    simpa only [hsplit g x] using hequivariant g y x
  exact nonempty_primePlusOrdinaryQuotient_of_RaynaudPeriodMap p hp ξ Y q
    hq hrank (fun g v => (hintertwine g v).trans (hperiodFixed g (q v))) m hm

end HilbertModularity.Hypergeometric
