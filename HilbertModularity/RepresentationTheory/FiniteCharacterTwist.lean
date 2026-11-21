/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.CoefficientPeriodTwist
public import HilbertModularity.RepresentationTheory.LabelledHodgeTate
public import HilbertModularity.NumberTheory.FiniteCharacter.PadicPeriods

/-! # Finite-order twists of local Hodge–Tate representations

Actual tensor periods of finite-order characters identify the canonical period
comparisons and weight-zero quotients before and after twisting. The local base
field and the coefficient field are independent extensions of `Q_p`.
The tower hypotheses use the algebra scalar actions explicitly, to distinguish
them from the completion’s independently inferred scalar actions.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace PadicComplex

variable (p : ℕ) [Fact p.Prime]
  {K : Type*} [Field K] [Algebra ℚ_[p] K] [Algebra K (PadicAlgCl p)]
  [IsScalarTower ℚ_[p] K (PadicAlgCl p)] [Algebra K ℂ_[p]]
  [hKC : @IsScalarTower K (PadicAlgCl p) ℂ_[p] Algebra.toSMul Algebra.toSMul Algebra.toSMul]

include hKC

/-- The actual local Galois action fixes the embedded local base in the completion. -/
theorem localGalois_fixes_base (g : Gal(PadicAlgCl p/K)) (a : K) :
    galoisEquiv p (g.restrictScalars ℚ_[p]) (algebraMap K ℂ_[p] a) =
      algebraMap K ℂ_[p] a := by
  rw [IsScalarTower.algebraMap_apply K (PadicAlgCl p) ℂ_[p]]
  exact galoisEquiv_coe_algebraMap_of_restrictScalars p g a

end PadicComplex

namespace HodgeTate

variable (p : ℕ) [Fact p.Prime]
  {K E V : Type*} [Field K] [Algebra ℚ_[p] K] [Algebra K (PadicAlgCl p)]
  [IsScalarTower ℚ_[p] K (PadicAlgCl p)] [Algebra K ℂ_[p]]
  [hKC : @IsScalarTower K (PadicAlgCl p) ℂ_[p] Algebra.toSMul Algebra.toSMul Algebra.toSMul] [hQKC : @IsScalarTower ℚ_[p] K ℂ_[p] Algebra.toSMul Algebra.toSMul Algebra.toSMul]
  [Field E] [Algebra ℚ_[p] E] [FiniteDimensional ℚ_[p] E]
  [TopologicalSpace Eˣ] [T1Space Eˣ]
  [AddCommGroup V] [Module E V] [Module ℚ_[p] V] [IsScalarTower ℚ_[p] E V]
  (ρ : Representation E Gal(PadicAlgCl p/K) V) (χ : Gal(PadicAlgCl p/K) →* Eˣ)
  (hχ : Continuous χ) (horder : IsOfFinOrder χ)

include hχ horder hKC hQKC

/-- Finite-order twists preserve the full canonical weight-zero comparison criterion. -/
theorem finiteCharacterTwist_comparison_and_weights_zero_iff :
    (Function.Bijective (comparison p (K := K) (AlgEquiv.restrictScalarsHom ℚ_[p])
        (PadicComplex.localGalois_fixes_base p (K := K)) (ρ.restrictScalars ℚ_[p])) ∧
      ∀ q : ℤ, q ≠ 0 → weightSpace p (AlgEquiv.restrictScalarsHom ℚ_[p])
        (ρ.restrictScalars ℚ_[p]) q = ⊥) ↔
    (Function.Bijective (comparison p (K := K) (AlgEquiv.restrictScalarsHom ℚ_[p])
        (PadicComplex.localGalois_fixes_base p (K := K)) ((ρ.characterTwist χ).restrictScalars ℚ_[p])) ∧
      ∀ q : ℤ, q ≠ 0 → weightSpace p (AlgEquiv.restrictScalarsHom ℚ_[p])
        ((ρ.characterTwist χ).restrictScalars ℚ_[p]) q = ⊥) := by
  obtain ⟨c, hc⟩ := PadicComplex.exists_local_tensor_period_of_continuous_isOfFinOrder
    p χ hχ horder
  exact coefficientTwist_comparison_and_weights_zero_iff p
    (AlgEquiv.restrictScalarsHom ℚ_[p]) (PadicComplex.localGalois_fixes_base p (K := K)) ρ χ c hc

/-- Tensoring by a continuous finite-order coefficient character preserves the existence
of a rank-one quotient with bijective comparison and all weights zero. -/
theorem finiteCharacterTensor_exists_weight_zero_quotient_iff :
    (∃ T : Subrepresentation ((Representation.ofCharacter χ).tprod ρ),
      Module.finrank E ((E ⊗[E] V) ⧸ T.toSubmodule) = 1 ∧
      Function.Bijective (comparison p (K := K) (AlgEquiv.restrictScalarsHom ℚ_[p]) (PadicComplex.localGalois_fixes_base p (K := K))
        ((((Representation.ofCharacter χ).tprod ρ).quotient
          T.toSubmodule T.apply_mem_toSubmodule).restrictScalars ℚ_[p])) ∧
      ∀ q : ℤ, q ≠ 0 → weightSpace p (AlgEquiv.restrictScalarsHom ℚ_[p])
        ((((Representation.ofCharacter χ).tprod ρ).quotient
          T.toSubmodule T.apply_mem_toSubmodule).restrictScalars ℚ_[p]) q = ⊥) ↔
    ∃ S : Subrepresentation ρ, Module.finrank E (V ⧸ S.toSubmodule) = 1 ∧
      Function.Bijective (comparison p (K := K) (AlgEquiv.restrictScalarsHom ℚ_[p]) (PadicComplex.localGalois_fixes_base p (K := K))
        ((ρ.quotient S.toSubmodule S.apply_mem_toSubmodule).restrictScalars ℚ_[p])) ∧
      ∀ q : ℤ, q ≠ 0 → weightSpace p (AlgEquiv.restrictScalarsHom ℚ_[p])
        ((ρ.quotient S.toSubmodule S.apply_mem_toSubmodule).restrictScalars ℚ_[p]) q = ⊥ := by
  obtain ⟨c, hc⟩ := PadicComplex.exists_local_tensor_period_of_continuous_isOfFinOrder
    p χ hχ horder
  exact coefficientCharacterTensor_exists_weight_zero_quotient_iff p
    (AlgEquiv.restrictScalarsHom ℚ_[p]) (PadicComplex.localGalois_fixes_base p (K := K)) ρ χ c hc

/-- Finite-order tensor twists preserve rank-one quotients with all nonzero weight spaces zero. -/
theorem finiteCharacterTensor_exists_quotient_weights_zero_iff :
    (∃ T : Subrepresentation ((Representation.ofCharacter χ).tprod ρ),
      Module.finrank E ((E ⊗[E] V) ⧸ T.toSubmodule) = 1 ∧
      ∀ q : ℤ, q ≠ 0 → weightSpace p (AlgEquiv.restrictScalarsHom ℚ_[p])
        ((((Representation.ofCharacter χ).tprod ρ).quotient
          T.toSubmodule T.apply_mem_toSubmodule).restrictScalars ℚ_[p]) q = ⊥) ↔
    ∃ S : Subrepresentation ρ, Module.finrank E (V ⧸ S.toSubmodule) = 1 ∧
      ∀ q : ℤ, q ≠ 0 → weightSpace p (AlgEquiv.restrictScalarsHom ℚ_[p])
        ((ρ.quotient S.toSubmodule S.apply_mem_toSubmodule).restrictScalars ℚ_[p]) q = ⊥ := by
  obtain ⟨c, hc⟩ := PadicComplex.exists_local_tensor_period_of_continuous_isOfFinOrder
    p χ hχ horder
  exact coefficientCharacterTensor_exists_quotient_weights_zero_iff p
    (AlgEquiv.restrictScalarsHom ℚ_[p]) (PadicComplex.localGalois_fixes_base p (K := K)) ρ χ c hc


variable [FiniteDimensional ℚ_[p] K]

/-- A continuous finite-order coefficient character preserves rank-one quotients whose
nonzero local-labelled period spaces vanish. For de Rham representations this is the
all-labelled weight-zero condition; the period-space statement needs no de Rham assumption. -/
theorem finiteCharacterTensor_exists_quotient_labelled_weights_zero_iff :
    (∃ T : Subrepresentation ((Representation.ofCharacter χ).tprod ρ),
      Module.finrank E ((E ⊗[E] V) ⧸ T.toSubmodule) = 1 ∧
      ∀ τ, ∀ q : ℤ, q ≠ 0 → labelledWeightSpace p
        (AlgEquiv.restrictScalarsHom ℚ_[p]) (PadicComplex.localGalois_fixes_base p (K := K))
        (((Representation.ofCharacter χ).tprod ρ).quotient
          T.toSubmodule T.apply_mem_toSubmodule) q τ = ⊥) ↔
    ∃ S : Subrepresentation ρ, Module.finrank E (V ⧸ S.toSubmodule) = 1 ∧
      ∀ τ, ∀ q : ℤ, q ≠ 0 → labelledWeightSpace p
        (AlgEquiv.restrictScalarsHom ℚ_[p]) (PadicComplex.localGalois_fixes_base p (K := K))
        (ρ.quotient S.toSubmodule S.apply_mem_toSubmodule) q τ = ⊥ :=
  (exists_quotient_labelled_weights_zero_iff p (AlgEquiv.restrictScalarsHom ℚ_[p])
    (PadicComplex.localGalois_fixes_base p (K := K)) ((Representation.ofCharacter χ).tprod ρ)).trans
    ((finiteCharacterTensor_exists_quotient_weights_zero_iff p ρ χ hχ horder).trans
      (exists_quotient_labelled_weights_zero_iff p (AlgEquiv.restrictScalarsHom ℚ_[p])
        (PadicComplex.localGalois_fixes_base p (K := K)) ρ).symm)

end HodgeTate
