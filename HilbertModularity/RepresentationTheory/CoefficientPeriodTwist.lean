/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.CharacterTwist
public import HilbertModularity.RepresentationTheory.HodgeTateFunctoriality
public import Mathlib.RingTheory.TensorProduct.Maps

/-! # Coefficient-tensor periods of character twists

The coefficient tensor `Cp ⊗[Qp] E` acts on the actual period tensor of an
`E`-representation. An invertible tensor period intertwines the completed
period actions before and after twisting by an `E`-valued character.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace HodgeTate

variable (p : ℕ) [Fact p.Prime]
  {E V G : Type*} [Field E] [Algebra ℚ_[p] E]
  [AddCommGroup V] [Module E V] [Module ℚ_[p] V] [IsScalarTower ℚ_[p] E V]
  [Group G] (ι : G →* (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p))

/-- The actual coefficient tensor acts linearly on the completed period tensor. -/
def periodCoefficientAction :
    ℂ_[p] ⊗[ℚ_[p]] E →ₐ[ℂ_[p]] Module.End ℂ_[p] (ℂ_[p] ⊗[ℚ_[p]] V) :=
  Algebra.TensorProduct.lift (Algebra.ofId ℂ_[p] _)
    ((Module.End.baseChangeHom ℚ_[p] ℂ_[p] V).comp (Algebra.lsmul ℚ_[p] ℚ_[p] V))
    (fun c _a => Algebra.commutes c _)

@[simp]
theorem periodCoefficientAction_tmul (c d : ℂ_[p]) (a : E) (v : V) :
    periodCoefficientAction p (c ⊗ₜ[ℚ_[p]] a) (d ⊗ₜ[ℚ_[p]] v) =
      (c * d) ⊗ₜ[ℚ_[p]] (a • v) := by
  change c • (d ⊗ₜ[ℚ_[p]] (a • v)) = _
  rw [TensorProduct.smul_tmul']
  rfl

/-- The Galois action on the coefficient tensor acts only on the completed period field. -/
def periodCoefficientGalois (g : G) : ℂ_[p] ⊗[ℚ_[p]] E →ₐ[ℚ_[p]] ℂ_[p] ⊗[ℚ_[p]] E :=
  Algebra.TensorProduct.map (PadicComplex.galoisEquiv p (ι g)).toAlgHom (AlgHom.id ℚ_[p] E)

/-- The period action is semilinear for the actual coefficient-tensor action. -/
theorem periodRepresentation_coefficientAction (ρ : Representation E G V) (g : G)
    (a : ℂ_[p] ⊗[ℚ_[p]] E) (x : ℂ_[p] ⊗[ℚ_[p]] V) :
    periodRepresentation p ι (ρ.restrictScalars ℚ_[p]) g (periodCoefficientAction p a x) =
      periodCoefficientAction p (periodCoefficientGalois p ι g a)
        (periodRepresentation p ι (ρ.restrictScalars ℚ_[p]) g x) := by
  induction a using TensorProduct.inductionOn with
  | tmul c a =>
      induction x using TensorProduct.inductionOn with
      | tmul d v =>
          change PadicComplex.galoisEquiv p (ι g) (c * d) ⊗ₜ[ℚ_[p]] ρ g (a • v) = _
          simp [periodCoefficientGalois, periodRepresentation_tmul, map_smul, Representation.restrictScalars]
      | add x y hx hy => simp only [map_add, hx, hy]
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]

/-- Twisting multiplies the period action by the coefficient character in the tensor algebra. -/
theorem periodRepresentation_coefficientTwist (ρ : Representation E G V) (χ : G →* Eˣ)
    (g : G) (x : ℂ_[p] ⊗[ℚ_[p]] V) :
    periodRepresentation p ι ((ρ.characterTwist χ).restrictScalars ℚ_[p]) g x =
      periodCoefficientAction p ((1 : ℂ_[p]) ⊗ₜ[ℚ_[p]] (χ g : E))
        (periodRepresentation p ι (ρ.restrictScalars ℚ_[p]) g x) := by
  induction x using TensorProduct.inductionOn with
  | tmul c v => simp [periodRepresentation_tmul, Representation.characterTwist_apply, Representation.restrictScalars]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- A unit of the coefficient tensor gives an actual invertible `Cp`-linear map. -/
def coefficientPeriodLinearEquiv (c : (ℂ_[p] ⊗[ℚ_[p]] E)ˣ) :
    (ℂ_[p] ⊗[ℚ_[p]] V) ≃ₗ[ℂ_[p]] (ℂ_[p] ⊗[ℚ_[p]] V) :=
  LinearEquiv.ofBijective (periodCoefficientAction p (c : ℂ_[p] ⊗[ℚ_[p]] E))
    ((Module.End.isUnit_iff _).mp (c.isUnit.map (periodCoefficientAction p (V := V))))

/-- A genuine tensor period intertwines the completed actions of a coefficient-valued twist. -/
theorem coefficientPeriodLinearEquiv_apply_action (ρ : Representation E G V) (χ : G →* Eˣ)
    (c : (ℂ_[p] ⊗[ℚ_[p]] E)ˣ)
    (hc : ∀ g, periodCoefficientGalois p ι g (c : ℂ_[p] ⊗[ℚ_[p]] E) *
      ((1 : ℂ_[p]) ⊗ₜ[ℚ_[p]] (χ g : E)) = c)
    (g : G) (x : ℂ_[p] ⊗[ℚ_[p]] V) :
    coefficientPeriodLinearEquiv p c (periodRepresentation p ι (ρ.restrictScalars ℚ_[p]) g x) =
      periodRepresentation p ι ((ρ.characterTwist χ).restrictScalars ℚ_[p]) g
        (coefficientPeriodLinearEquiv p c x) := by
  change periodCoefficientAction p (c : ℂ_[p] ⊗[ℚ_[p]] E)
    (periodRepresentation p ι (ρ.restrictScalars ℚ_[p]) g x) =
      periodRepresentation p ι ((ρ.characterTwist χ).restrictScalars ℚ_[p]) g
        (periodCoefficientAction p (c : ℂ_[p] ⊗[ℚ_[p]] E) x)
  rw [periodRepresentation_coefficientTwist, periodRepresentation_coefficientAction]
  change _ = (periodCoefficientAction p (V := V) ((1 : ℂ_[p]) ⊗ₜ[ℚ_[p]] (χ g : E)) *
    periodCoefficientAction p (V := V) (periodCoefficientGalois p ι g (c : ℂ_[p] ⊗[ℚ_[p]] E)))
      (periodRepresentation p ι (ρ.restrictScalars ℚ_[p]) g x)
  rw [← map_mul, mul_comm, hc]

section Comparison

variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [Algebra K ℂ_[p]]
  [IsScalarTower ℚ_[p] K ℂ_[p]]
  (hK : ∀ (g : G) (a : K), PadicComplex.galoisEquiv p (ι g)
    (algebraMap K ℂ_[p] a) = algebraMap K ℂ_[p] a)
  (ρ : Representation E G V) (χ : G →* Eˣ) (c : (ℂ_[p] ⊗[ℚ_[p]] E)ˣ)
  (hc : ∀ g, periodCoefficientGalois p ι g (c : ℂ_[p] ⊗[ℚ_[p]] E) *
    ((1 : ℂ_[p]) ⊗ₜ[ℚ_[p]] (χ g : E)) = c)

include hK hc

/-- A genuine coefficient-tensor period preserves bijectivity of the canonical comparison. -/
theorem coefficientTwist_comparison_bijective_iff :
    Function.Bijective (comparison p ι hK (ρ.restrictScalars ℚ_[p])) ↔
      Function.Bijective (comparison p ι hK ((ρ.characterTwist χ).restrictScalars ℚ_[p])) :=
  comparison_bijective_periodEquiv_iff p ι hK (coefficientPeriodLinearEquiv p c)
    (coefficientPeriodLinearEquiv_apply_action p ι ρ χ c hc)

/-- A genuine coefficient-tensor period preserves vanishing of every actual weight space. -/
theorem coefficientTwist_weightSpace_eq_bot_iff (q : ℤ) :
    weightSpace p ι (ρ.restrictScalars ℚ_[p]) q = ⊥ ↔
      weightSpace p ι ((ρ.characterTwist χ).restrictScalars ℚ_[p]) q = ⊥ := by
  rw [← Submodule.subsingleton_iff_eq_bot, ← Submodule.subsingleton_iff_eq_bot]
  exact (localWeightSpacePeriodEquiv p ι hK (coefficientPeriodLinearEquiv p c)
    (coefficientPeriodLinearEquiv_apply_action p ι ρ χ c hc) q).toEquiv.subsingleton_congr

/-- The same tensor period preserves the full actual weight-zero comparison criterion. -/
theorem coefficientTwist_comparison_and_weights_zero_iff :
    (Function.Bijective (comparison p ι hK (ρ.restrictScalars ℚ_[p])) ∧
      ∀ q : ℤ, q ≠ 0 → weightSpace p ι (ρ.restrictScalars ℚ_[p]) q = ⊥) ↔
    (Function.Bijective (comparison p ι hK ((ρ.characterTwist χ).restrictScalars ℚ_[p])) ∧
      ∀ q : ℤ, q ≠ 0 → weightSpace p ι ((ρ.characterTwist χ).restrictScalars ℚ_[p]) q = ⊥) :=
  and_congr (coefficientTwist_comparison_bijective_iff p ι hK ρ χ c hc)
    (forall_congr' fun q => imp_congr_right fun _ =>
      coefficientTwist_weightSpace_eq_bot_iff p ι hK ρ χ c hc q)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- A genuine coefficient-tensor period preserves rank-one quotients with
bijective Hodge–Tate comparison and vanishing nonzero weight spaces. -/
theorem coefficientCharacterTensor_exists_weight_zero_quotient_iff :
    (∃ T : Subrepresentation ((Representation.ofCharacter χ).tprod ρ),
      Module.finrank E ((E ⊗[E] V) ⧸ T.toSubmodule) = 1 ∧
      Function.Bijective (comparison p ι hK
        ((((Representation.ofCharacter χ).tprod ρ).quotient
          T.toSubmodule T.apply_mem_toSubmodule).restrictScalars ℚ_[p])) ∧
      ∀ q : ℤ, q ≠ 0 → weightSpace p ι
        ((((Representation.ofCharacter χ).tprod ρ).quotient
          T.toSubmodule T.apply_mem_toSubmodule).restrictScalars ℚ_[p]) q = ⊥) ↔
    ∃ S : Subrepresentation ρ, Module.finrank E (V ⧸ S.toSubmodule) = 1 ∧
      Function.Bijective (comparison p ι hK
        ((ρ.quotient S.toSubmodule S.apply_mem_toSubmodule).restrictScalars ℚ_[p])) ∧
      ∀ q : ℤ, q ≠ 0 → weightSpace p ι
        ((ρ.quotient S.toSubmodule S.apply_mem_toSubmodule).restrictScalars ℚ_[p]) q = ⊥ := by
  have hcrit (S : Subrepresentation ρ) :
      (Function.Bijective (comparison p ι hK
        ((((Representation.ofCharacter χ).tprod ρ).quotient
          (Representation.characterTensorSubrepresentationEquiv ρ χ S).toSubmodule
          (Representation.characterTensorSubrepresentationEquiv ρ χ S).apply_mem_toSubmodule).restrictScalars ℚ_[p])) ∧
        ∀ q : ℤ, q ≠ 0 → weightSpace p ι
          ((((Representation.ofCharacter χ).tprod ρ).quotient
            (Representation.characterTensorSubrepresentationEquiv ρ χ S).toSubmodule
            (Representation.characterTensorSubrepresentationEquiv ρ χ S).apply_mem_toSubmodule).restrictScalars ℚ_[p]) q = ⊥) ↔
      (Function.Bijective (comparison p ι hK
        ((ρ.quotient S.toSubmodule S.apply_mem_toSubmodule).restrictScalars ℚ_[p])) ∧
        ∀ q : ℤ, q ≠ 0 → weightSpace p ι
          ((ρ.quotient S.toSubmodule S.apply_mem_toSubmodule).restrictScalars ℚ_[p]) q = ⊥) := by
    let e := ((Representation.characterTensorQuotientEquiv ρ χ S).trans
      (Representation.characterTwistTensorEquiv
        (ρ.quotient S.toSubmodule S.apply_mem_toSubmodule) χ)).restrictScalars ℚ_[p]
    exact (and_congr (comparison_bijective_iff p ι hK e)
      (forall_congr' fun q => imp_congr_right fun _ => weightSpace_eq_bot_iff (ι := ι) e q)).trans
      (coefficientTwist_comparison_and_weights_zero_iff p ι hK
        (ρ.quotient S.toSubmodule S.apply_mem_toSubmodule) χ c hc).symm
  constructor
  · rintro ⟨T, hdim, hT⟩
    obtain ⟨S, rfl⟩ := (Representation.characterTensorSubrepresentationEquiv ρ χ).surjective T
    exact ⟨S, (Representation.finrank_characterTensor_quotient ρ χ S).symm.trans hdim,
      (hcrit S).mp hT⟩
  · rintro ⟨S, hdim, hS⟩
    exact ⟨Representation.characterTensorSubrepresentationEquiv ρ χ S,
      (Representation.finrank_characterTensor_quotient ρ χ S).trans hdim, (hcrit S).mpr hS⟩


set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- A tensor period preserves rank-one quotients whose nonzero actual weight spaces vanish.
This statement does not require a comparison-map hypothesis. -/
theorem coefficientCharacterTensor_exists_quotient_weights_zero_iff :
    (∃ T : Subrepresentation ((Representation.ofCharacter χ).tprod ρ),
      Module.finrank E ((E ⊗[E] V) ⧸ T.toSubmodule) = 1 ∧
      ∀ q : ℤ, q ≠ 0 → weightSpace p ι
        ((((Representation.ofCharacter χ).tprod ρ).quotient
          T.toSubmodule T.apply_mem_toSubmodule).restrictScalars ℚ_[p]) q = ⊥) ↔
    ∃ S : Subrepresentation ρ, Module.finrank E (V ⧸ S.toSubmodule) = 1 ∧
      ∀ q : ℤ, q ≠ 0 → weightSpace p ι
        ((ρ.quotient S.toSubmodule S.apply_mem_toSubmodule).restrictScalars ℚ_[p]) q = ⊥ := by
  have hcrit (S : Subrepresentation ρ) :
      (∀ q : ℤ, q ≠ 0 → weightSpace p ι
        ((((Representation.ofCharacter χ).tprod ρ).quotient
          (Representation.characterTensorSubrepresentationEquiv ρ χ S).toSubmodule
          (Representation.characterTensorSubrepresentationEquiv ρ χ S).apply_mem_toSubmodule).restrictScalars ℚ_[p]) q = ⊥) ↔
      (∀ q : ℤ, q ≠ 0 → weightSpace p ι
        ((ρ.quotient S.toSubmodule S.apply_mem_toSubmodule).restrictScalars ℚ_[p]) q = ⊥) := by
    let e := ((Representation.characterTensorQuotientEquiv ρ χ S).trans
      (Representation.characterTwistTensorEquiv
        (ρ.quotient S.toSubmodule S.apply_mem_toSubmodule) χ)).restrictScalars ℚ_[p]
    apply forall_congr'
    intro q
    apply imp_congr_right
    intro _
    exact (weightSpace_eq_bot_iff (ι := ι) e q).trans
      (coefficientTwist_weightSpace_eq_bot_iff p ι hK
        (ρ.quotient S.toSubmodule S.apply_mem_toSubmodule) χ c hc q).symm
  constructor
  · rintro ⟨T, hdim, hT⟩
    obtain ⟨S, rfl⟩ := (Representation.characterTensorSubrepresentationEquiv ρ χ).surjective T
    exact ⟨S, (Representation.finrank_characterTensor_quotient ρ χ S).symm.trans hdim,
      (hcrit S).mp hT⟩
  · rintro ⟨S, hdim, hS⟩
    exact ⟨Representation.characterTensorSubrepresentationEquiv ρ χ S,
      (Representation.finrank_characterTensor_quotient ρ χ S).trans hdim, (hcrit S).mpr hS⟩

end Comparison

end HodgeTate
