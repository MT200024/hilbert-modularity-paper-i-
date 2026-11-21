/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.CharacterTwist
public import HilbertModularity.RepresentationTheory.HodgeTate

/-! # Period trivializations of character twists

An actual nonzero period of a character gives an intertwining equivalence
between the period tensors before and after twisting. No assertion that finite
characters possess such periods is assumed or proved here.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace HodgeTate

variable (p : ℕ) [Fact p.Prime]
variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℚ_[p] V]
variable (ι : G →* (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p))

/-- A rational p-adic scalar character multiplies the period action by that character. -/
theorem periodRepresentation_characterTwist (ρ : Representation ℚ_[p] G V)
    (χ : G →* ℚ_[p]ˣ) (g : G) (x : ℂ_[p] ⊗[ℚ_[p]] V) :
    periodRepresentation p ι (ρ.characterTwist χ) g x =
      (χ g : ℚ_[p]) • periodRepresentation p ι ρ g x := by
  induction x using TensorProduct.inductionOn with
  | tmul a v =>
      change PadicComplex.galoisEquiv p (ι g) a ⊗ₜ[ℚ_[p]] ((χ g : ℚ_[p]) • ρ g v) =
        (χ g : ℚ_[p]) • (PadicComplex.galoisEquiv p (ι g) a ⊗ₜ[ℚ_[p]] ρ g v)
      exact TensorProduct.tmul_smul _ _ _
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]

/-- Multiplication by an actual character period intertwines the two diagonal actions. -/
def characterTwistPeriodEquiv (ρ : Representation ℚ_[p] G V) (χ : G →* ℚ_[p]ˣ)
    (c : ℂ_[p]ˣ)
    (hc : ∀ g, PadicComplex.galoisEquiv p (ι g) (c : ℂ_[p]) *
      algebraMap ℚ_[p] ℂ_[p] (χ g : ℚ_[p]) = c) :
    (periodRepresentation p ι ρ).Equiv
      (periodRepresentation p ι (ρ.characterTwist χ)) :=
  .mk ((LinearEquiv.smulOfUnit c).restrictScalars ℚ_[p]) (by
    intro g
    apply LinearMap.ext
    intro x
    change (c : ℂ_[p]) • periodRepresentation p ι ρ g x =
      periodRepresentation p ι (ρ.characterTwist χ) g ((c : ℂ_[p]) • x)
    rw [periodRepresentation_smul, periodRepresentation_characterTwist,
      ← algebraMap_smul ℂ_[p] (χ g : ℚ_[p]), smul_smul, hc])

/-- The same actual period preserves every cyclotomic eigenspace under the twist. -/
theorem characterTwistPeriodEquiv_mem_weightSpace_iff
    (ρ : Representation ℚ_[p] G V) (χ : G →* ℚ_[p]ˣ) (c : ℂ_[p]ˣ)
    (hc : ∀ g, PadicComplex.galoisEquiv p (ι g) (c : ℂ_[p]) *
      algebraMap ℚ_[p] ℂ_[p] (χ g : ℚ_[p]) = c)
    (q : ℤ) (x : ℂ_[p] ⊗[ℚ_[p]] V) :
    characterTwistPeriodEquiv p ι ρ χ c hc x ∈ weightSpace p ι (ρ.characterTwist χ) q ↔
      x ∈ weightSpace p ι ρ q := by
  simp only [mem_weightSpace]
  apply forall_congr'
  intro g
  let e := characterTwistPeriodEquiv p ι ρ χ c hc
  have he : e (periodRepresentation p ι ρ g x) =
      periodRepresentation p ι (ρ.characterTwist χ) g (e x) :=
    congrArg (fun f : (ℂ_[p] ⊗[ℚ_[p]] V) →ₗ[ℚ_[p]] (ℂ_[p] ⊗[ℚ_[p]] V) => f x)
      (e.isIntertwining' g)
  change _ = _ ↔ _ = _
  rw [← he, ← map_smul e]
  exact e.toLinearEquiv.injective.eq_iff

/-- Multiplication by the period identifies the concrete weight spaces linearly. -/
def characterTwistWeightSpaceEquiv (ρ : Representation ℚ_[p] G V) (χ : G →* ℚ_[p]ˣ)
    (c : ℂ_[p]ˣ)
    (hc : ∀ g, PadicComplex.galoisEquiv p (ι g) (c : ℂ_[p]) *
      algebraMap ℚ_[p] ℂ_[p] (χ g : ℚ_[p]) = c) (q : ℤ) :
    weightSpace p ι ρ q ≃ₗ[ℚ_[p]] weightSpace p ι (ρ.characterTwist χ) q :=
  (characterTwistPeriodEquiv p ι ρ χ c hc).toLinearEquiv.ofSubmodules _ _ (by
    ext y
    let e := characterTwistPeriodEquiv p ι ρ χ c hc
    obtain ⟨x, rfl⟩ := e.toLinearEquiv.surjective y
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨z, hz, he⟩
      have hzx : z = x := e.toLinearEquiv.injective he
      exact (characterTwistPeriodEquiv_mem_weightSpace_iff p ι ρ χ c hc q x).mpr (hzx ▸ hz)
    · intro hx
      exact ⟨x, (characterTwistPeriodEquiv_mem_weightSpace_iff p ι ρ χ c hc q x).mp hx, rfl⟩)

/-- A nonzero actual period makes the fixed-period spans of a character twist equal. -/
theorem zeroWeightSpan_characterTwist (ρ : Representation ℚ_[p] G V) (χ : G →* ℚ_[p]ˣ)
    (c : ℂ_[p]ˣ)
    (hc : ∀ g, PadicComplex.galoisEquiv p (ι g) (c : ℂ_[p]) *
      algebraMap ℚ_[p] ℂ_[p] (χ g : ℚ_[p]) = c) :
    zeroWeightSpan (ι := ι) (ρ.characterTwist χ) = zeroWeightSpan (ι := ι) ρ := by
  let e := characterTwistPeriodEquiv p ι ρ χ c hc
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro x hx
    have hy : e.toLinearEquiv.symm x ∈ weightSpace p ι ρ 0 := by
      apply (characterTwistPeriodEquiv_mem_weightSpace_iff p ι ρ χ c hc 0 _).mp
      change e.toLinearEquiv (e.toLinearEquiv.symm x) ∈ weightSpace p ι (ρ.characterTwist χ) 0
      rw [e.toLinearEquiv.apply_symm_apply]
      exact hx
    have he : (c : ℂ_[p]) • e.toLinearEquiv.symm x = x := e.toLinearEquiv.apply_symm_apply x
    rw [← he]
    exact (zeroWeightSpan (ι := ι) ρ).smul_mem (c : ℂ_[p]) (Submodule.subset_span hy)
  · apply Submodule.span_le.mpr
    intro x hx
    change x ∈ zeroWeightSpan (ι := ι) (ρ.characterTwist χ)
    have hy := (characterTwistPeriodEquiv_mem_weightSpace_iff p ι ρ χ c hc 0 x).mpr hx
    have hs : (c : ℂ_[p]) • x ∈ zeroWeightSpan (ι := ι) (ρ.characterTwist χ) :=
      Submodule.subset_span hy
    have h := (zeroWeightSpan (ι := ι) (ρ.characterTwist χ)).smul_mem
      ((c⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) hs
    simpa only [smul_smul, Units.inv_mul, one_smul] using h

/-- Tensoring by a character with an actual nonzero period preserves fixed-period spanning. -/
theorem zeroWeightSpan_characterTensor_eq_top_iff
    (ρ : Representation ℚ_[p] G V) (χ : G →* ℚ_[p]ˣ) (c : ℂ_[p]ˣ)
    (hc : ∀ g, PadicComplex.galoisEquiv p (ι g) (c : ℂ_[p]) *
      algebraMap ℚ_[p] ℂ_[p] (χ g : ℚ_[p]) = c) :
    zeroWeightSpan (ι := ι) ((Representation.ofCharacter χ).tprod ρ) = ⊤ ↔
      zeroWeightSpan (ι := ι) ρ = ⊤ := by
  rw [zeroWeightSpan_eq_top_iff (Representation.characterTwistTensorEquiv ρ χ),
    zeroWeightSpan_characterTwist p ι ρ χ c hc]

/-- An actual character period preserves existence of a fixed-period rank-one quotient. -/
theorem characterTensor_exists_quotient_spanned_by_fixed_periods_iff
    (ρ : Representation ℚ_[p] G V) (χ : G →* ℚ_[p]ˣ) (c : ℂ_[p]ˣ)
    (hc : ∀ g, PadicComplex.galoisEquiv p (ι g) (c : ℂ_[p]) *
      algebraMap ℚ_[p] ℂ_[p] (χ g : ℚ_[p]) = c) :
    (∃ T : Subrepresentation ((Representation.ofCharacter χ).tprod ρ),
      Module.finrank ℚ_[p] ((ℚ_[p] ⊗[ℚ_[p]] V) ⧸ T.toSubmodule) = 1 ∧
      zeroWeightSpan (ι := ι) (((Representation.ofCharacter χ).tprod ρ).quotient
        T.toSubmodule T.apply_mem_toSubmodule) = ⊤) ↔
    ∃ S : Subrepresentation ρ, Module.finrank ℚ_[p] (V ⧸ S.toSubmodule) = 1 ∧
      zeroWeightSpan (ι := ι) (ρ.quotient S.toSubmodule S.apply_mem_toSubmodule) = ⊤ := by
  have hspan (S : Subrepresentation ρ) :
      zeroWeightSpan (ι := ι) (((Representation.ofCharacter χ).tprod ρ).quotient
        (Representation.characterTensorSubrepresentationEquiv ρ χ S).toSubmodule
        (Representation.characterTensorSubrepresentationEquiv ρ χ S).apply_mem_toSubmodule) = ⊤ ↔
      zeroWeightSpan (ι := ι) (ρ.quotient S.toSubmodule S.apply_mem_toSubmodule) = ⊤ :=
    (zeroWeightSpan_eq_top_iff (ι := ι) (Representation.characterTensorQuotientEquiv ρ χ S)).trans
      (zeroWeightSpan_characterTensor_eq_top_iff p ι
        (ρ.quotient S.toSubmodule S.apply_mem_toSubmodule) χ c hc)
  constructor
  · rintro ⟨T, hdim, hT⟩
    obtain ⟨S, rfl⟩ := (Representation.characterTensorSubrepresentationEquiv ρ χ).surjective T
    exact ⟨S, (Representation.finrank_characterTensor_quotient ρ χ S).symm.trans hdim,
      (hspan S).mp hT⟩
  · rintro ⟨S, hdim, hS⟩
    exact ⟨Representation.characterTensorSubrepresentationEquiv ρ χ S,
      (Representation.finrank_characterTensor_quotient ρ χ S).trans hdim, (hspan S).mpr hS⟩

end HodgeTate
