/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.HodgeTate
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Algebra.DirectSum.Module

/-! # Hodge–Tate comparison maps

The weight spaces over a base field fixed by the local Galois action have
canonical scalar-extension maps into the actual completed period tensor.
We follow [src_brinon_conrad, Remark 2.3.2]. Bijectivity of a comparison map
is a mathematical condition on this map, and is not asserted in this file.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace HodgeTate

variable (p : ℕ) [Fact p.Prime]
variable {K G V : Type*} [Field K] [Algebra ℚ_[p] K] [Algebra K ℂ_[p]]
  [IsScalarTower ℚ_[p] K ℂ_[p]] [Group G] [AddCommGroup V] [Module ℚ_[p] V]
variable (ι : G →* (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p))
variable (hK : ∀ (g : G) (a : K),
  PadicComplex.galoisEquiv p (ι g) (algebraMap K ℂ_[p] a) = algebraMap K ℂ_[p] a)

/-- The concrete cyclotomic period eigenspace, linear over the fixed local base field. -/
def localWeightSpace (ρ : Representation ℚ_[p] G V) (q : ℤ) :
    Submodule K (ℂ_[p] ⊗[ℚ_[p]] V) where
  carrier := weightSpace p ι ρ q
  zero_mem' := (weightSpace p ι ρ q).zero_mem
  add_mem' := (weightSpace p ι ρ q).add_mem
  smul_mem' a x hx := by
    change x ∈ weightSpace p ι ρ q at hx
    change a • x ∈ weightSpace p ι ρ q
    rw [mem_weightSpace] at hx ⊢
    intro g
    rw [← algebraMap_smul ℂ_[p] a x, periodRepresentation_smul, hK, hx g,
      smul_comm]

/-- Extending a weight space to `Cp` sends a pure tensor to its scalar multiple
inside the original period tensor. -/
def weightComparison (ρ : Representation ℚ_[p] G V) (q : ℤ) :
    (ℂ_[p] ⊗[K] localWeightSpace p ι hK ρ q) →ₗ[ℂ_[p]] (ℂ_[p] ⊗[ℚ_[p]] V) :=
  (localWeightSpace p ι hK ρ q).subtype.liftBaseChange ℂ_[p]

@[simp]
theorem weightComparison_tmul (ρ : Representation ℚ_[p] G V) (q : ℤ)
    (c : ℂ_[p]) (x : localWeightSpace p ι hK ρ q) :
    weightComparison p ι hK ρ q (c ⊗ₜ[K] x) = c • (x : ℂ_[p] ⊗[ℚ_[p]] V) := rfl

/-- The Hodge–Tate comparison map is the sum of the actual scalar-extension maps. -/
def comparison (ρ : Representation ℚ_[p] G V) :
    (DirectSum ℤ (fun q => ℂ_[p] ⊗[K] localWeightSpace p ι hK ρ q)) →ₗ[ℂ_[p]]
      (ℂ_[p] ⊗[ℚ_[p]] V) :=
  DirectSum.toModule ℂ_[p] ℤ (ℂ_[p] ⊗[ℚ_[p]] V) (weightComparison p ι hK ρ)

/-- On each summand the comparison map is the scalar-extension multiplication map. -/
@[simp]
theorem comparison_lof (ρ : Representation ℚ_[p] G V) (q : ℤ)
    (x : ℂ_[p] ⊗[K] localWeightSpace p ι hK ρ q) :
    comparison p ι hK ρ (DirectSum.lof ℂ_[p] ℤ
      (fun q => ℂ_[p] ⊗[K] localWeightSpace p ι hK ρ q) q x) =
      weightComparison p ι hK ρ q x := by
  simp [comparison]

/-- The image of one weight summand is exactly the `Cp` span of its actual periods. -/
theorem range_weightComparison (ρ : Representation ℚ_[p] G V) (q : ℤ) :
    LinearMap.range (weightComparison p ι hK ρ q) =
      Submodule.span ℂ_[p] (weightSpace p ι ρ q : Set (ℂ_[p] ⊗[ℚ_[p]] V)) := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    induction x using TensorProduct.inductionOn with
    | tmul c v =>
        exact Submodule.smul_mem _ c (Submodule.subset_span v.property)
    | add x y hx hy =>
        rw [map_add]
        exact Submodule.add_mem _ hx hy
  · apply Submodule.span_le.mpr
    intro x hx
    refine ⟨1 ⊗ₜ[K] (⟨x, hx⟩ : localWeightSpace p ι hK ρ q), ?_⟩
    simp

/-- Distinct weight summands have disjoint images whenever the actual comparison is injective. -/
theorem disjoint_range_weightComparison (ρ : Representation ℚ_[p] G V)
    (hinj : Function.Injective (comparison p ι hK ρ)) {q r : ℤ} (hqr : q ≠ r) :
    Disjoint (LinearMap.range (weightComparison p ι hK ρ q))
      (LinearMap.range (weightComparison p ι hK ρ r)) := by
  rw [Submodule.disjoint_def]
  rintro z ⟨x, hx⟩ ⟨y, hy⟩
  have he : DirectSum.lof ℂ_[p] ℤ
      (fun q => ℂ_[p] ⊗[K] localWeightSpace p ι hK ρ q) q x =
      DirectSum.lof ℂ_[p] ℤ
      (fun q => ℂ_[p] ⊗[K] localWeightSpace p ι hK ρ q) r y := by
    apply hinj
    simpa only [comparison_lof] using hx.trans hy.symm
  have hx0 : x = 0 := by
    have h := congrArg (fun z => z q) he
    simpa [DirectSum.lof_eq_of, DirectSum.of_apply, hqr.symm] using h
  rw [hx0, map_zero] at hx
  exact hx.symm

/-- A nonzero period of nonzero weight prevents fixed periods from spanning,
provided that the concrete Hodge–Tate comparison map is injective. -/
theorem zeroWeightSpan_ne_top_of_injective_comparison
    (ρ : Representation ℚ_[p] G V) (hinj : Function.Injective (comparison p ι hK ρ))
    {q : ℤ} (hq : q ≠ 0) {x : ℂ_[p] ⊗[ℚ_[p]] V}
    (hx : x ∈ weightSpace p ι ρ q) (hx0 : x ≠ 0) :
    zeroWeightSpan (ι := ι) ρ ≠ ⊤ := by
  intro htop
  have hd := disjoint_range_weightComparison p ι hK ρ hinj hq.symm
  rw [range_weightComparison, range_weightComparison] at hd
  apply hx0
  apply Submodule.disjoint_def.mp hd
  · change x ∈ zeroWeightSpan (ι := ι) ρ
    rw [htop]
    trivial
  · exact Submodule.subset_span hx

/-- If the concrete comparison is surjective and every nonzero weight space vanishes,
fixed periods span the whole completed tensor. -/
theorem zeroWeightSpan_eq_top_of_surjective_comparison
    (ρ : Representation ℚ_[p] G V) (hsurj : Function.Surjective (comparison p ι hK ρ))
    (hweights : ∀ q : ℤ, q ≠ 0 → weightSpace p ι ρ q = ⊥) :
    zeroWeightSpan (ι := ι) ρ = ⊤ := by
  apply top_unique
  intro x hx
  clear hx
  obtain ⟨z, rfl⟩ := hsurj x
  induction z using DirectSum.induction_on with
  | zero => simp
  | of q z =>
      change comparison p ι hK ρ (DirectSum.lof ℂ_[p] ℤ
        (fun q => ℂ_[p] ⊗[K] localWeightSpace p ι hK ρ q) q z) ∈ zeroWeightSpan (ι := ι) ρ
      rw [comparison_lof]
      have hz : weightComparison p ι hK ρ q z ∈
          Submodule.span ℂ_[p] (weightSpace p ι ρ q : Set (ℂ_[p] ⊗[ℚ_[p]] V)) := by
        rw [← range_weightComparison p ι hK ρ q]
        exact ⟨z, rfl⟩
      by_cases hq : q = 0
      · subst q
        exact hz
      · rw [hweights q hq] at hz
        have he : weightComparison p ι hK ρ q z = 0 := by simpa using hz
        rw [he]
        exact Submodule.zero_mem _
  | add x y hx hy =>
      rw [map_add]
      exact Submodule.add_mem _ hx hy

/-- If fixed periods span, the concrete Hodge–Tate comparison map is surjective. -/
theorem comparison_surjective_of_zeroWeightSpan_eq_top
    (ρ : Representation ℚ_[p] G V) (hspan : zeroWeightSpan (ι := ι) ρ = ⊤) :
    Function.Surjective (comparison p ι hK ρ) := by
  intro x
  have hx : x ∈ LinearMap.range (weightComparison p ι hK ρ 0) := by
    rw [range_weightComparison]
    change x ∈ zeroWeightSpan (ι := ι) ρ
    rw [hspan]
    trivial
  obtain ⟨y, hy⟩ := hx
  exact ⟨DirectSum.lof ℂ_[p] ℤ
    (fun q => ℂ_[p] ⊗[K] localWeightSpace p ι hK ρ q) 0 y,
    (comparison_lof p ι hK ρ 0 y).trans hy⟩

/-- Under injectivity of the actual comparison map, fixed periods spanning
forces every nonzero cyclotomic weight space to vanish. -/
theorem weightSpace_eq_bot_of_zeroWeightSpan_eq_top
    (ρ : Representation ℚ_[p] G V) (hinj : Function.Injective (comparison p ι hK ρ))
    (hspan : zeroWeightSpan (ι := ι) ρ = ⊤) {q : ℤ} (hq : q ≠ 0) :
    weightSpace p ι ρ q = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  by_contra hx0
  exact zeroWeightSpan_ne_top_of_injective_comparison p ι hK ρ hinj hq hx hx0 hspan

/-- With injective comparison, the fixed-period criterion is exactly
bijectivity of comparison with no nonzero Hodge–Tate weights. -/
theorem zeroWeightSpan_eq_top_iff_comparison_bijective_and_weights_zero
    (ρ : Representation ℚ_[p] G V) (hinj : Function.Injective (comparison p ι hK ρ)) :
    zeroWeightSpan (ι := ι) ρ = ⊤ ↔
      Function.Bijective (comparison p ι hK ρ) ∧
        ∀ q : ℤ, q ≠ 0 → weightSpace p ι ρ q = ⊥ := by
  constructor
  · intro hspan
    exact ⟨⟨hinj, comparison_surjective_of_zeroWeightSpan_eq_top p ι hK ρ hspan⟩,
      fun _ hq => weightSpace_eq_bot_of_zeroWeightSpan_eq_top p ι hK ρ hinj hspan hq⟩
  · rintro ⟨hbij, hweights⟩
    exact zeroWeightSpan_eq_top_of_surjective_comparison p ι hK ρ hbij.2 hweights

section Equivalences

variable {W : Type*} [AddCommGroup W] [Module ℚ_[p] W]
  {ρ : Representation ℚ_[p] G V} {τ : Representation ℚ_[p] G W}

/-- An intertwining equivalence identifies period spaces over the fixed local base field. -/
def localWeightSpaceEquiv (e : ρ.Equiv τ) (q : ℤ) :
    localWeightSpace p ι hK ρ q ≃ₗ[K] localWeightSpace p ι hK τ q :=
  ((periodLinearEquiv e).restrictScalars K).ofSubmodules _ _ (by
    ext y
    obtain ⟨x, rfl⟩ := (periodLinearEquiv e).surjective y
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨z, hz, he⟩
      have hzx : z = x := (periodLinearEquiv e).injective he
      change periodLinearEquiv e x ∈ weightSpace p ι τ q
      rw [periodLinearEquiv_apply]
      exact (periodEquiv_mem_weightSpace_iff e q x).mpr (hzx ▸ hz)
    · intro hx
      refine ⟨x, ?_, rfl⟩
      change periodLinearEquiv e x ∈ weightSpace p ι τ q at hx
      rw [periodLinearEquiv_apply] at hx
      exact (periodEquiv_mem_weightSpace_iff e q x).mp hx)

/-- Extend the actual weight-space equivalence to `Cp`. -/
def weightComparisonSourceEquiv (e : ρ.Equiv τ) (q : ℤ) :
    (ℂ_[p] ⊗[K] localWeightSpace p ι hK ρ q) ≃ₗ[ℂ_[p]]
      (ℂ_[p] ⊗[K] localWeightSpace p ι hK τ q) :=
  TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl ℂ_[p] ℂ_[p])
    (localWeightSpaceEquiv p ι hK e q)

/-- The scalar-extension multiplication comparison commutes with intertwining equivalences. -/
theorem weightComparison_natural (e : ρ.Equiv τ) (q : ℤ)
    (x : ℂ_[p] ⊗[K] localWeightSpace p ι hK ρ q) :
    weightComparison p ι hK τ q (weightComparisonSourceEquiv p ι hK e q x) =
      periodLinearEquiv e (weightComparison p ι hK ρ q x) := by
  induction x using TensorProduct.inductionOn with
  | tmul c x => exact ((periodLinearEquiv e).map_smul c x).symm
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The direct sum of the actual scalar-extended weight-space equivalences. -/
def comparisonSourceEquiv (e : ρ.Equiv τ) :
    (DirectSum ℤ (fun q => ℂ_[p] ⊗[K] localWeightSpace p ι hK ρ q)) ≃ₗ[ℂ_[p]]
      (DirectSum ℤ (fun q => ℂ_[p] ⊗[K] localWeightSpace p ι hK τ q)) :=
  DirectSum.congrLinearEquiv (weightComparisonSourceEquiv p ι hK e)

@[simp]
theorem comparisonSourceEquiv_lof (e : ρ.Equiv τ) (q : ℤ)
    (x : ℂ_[p] ⊗[K] localWeightSpace p ι hK ρ q) :
    comparisonSourceEquiv p ι hK e (DirectSum.lof ℂ_[p] ℤ
      (fun q => ℂ_[p] ⊗[K] localWeightSpace p ι hK ρ q) q x) =
      DirectSum.lof ℂ_[p] ℤ (fun q => ℂ_[p] ⊗[K] localWeightSpace p ι hK τ q) q
        (weightComparisonSourceEquiv p ι hK e q x) := by
  simp [comparisonSourceEquiv, DirectSum.coe_congrLinearEquiv]

/-- The entire comparison map commutes with an intertwining equivalence. -/
theorem comparison_natural (e : ρ.Equiv τ)
    (x : DirectSum ℤ (fun q => ℂ_[p] ⊗[K] localWeightSpace p ι hK ρ q)) :
    comparison p ι hK τ (comparisonSourceEquiv p ι hK e x) =
      periodLinearEquiv e (comparison p ι hK ρ x) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of q x =>
      change comparison p ι hK τ (comparisonSourceEquiv p ι hK e
        (DirectSum.lof ℂ_[p] ℤ (fun q => ℂ_[p] ⊗[K] localWeightSpace p ι hK ρ q) q x)) =
        periodLinearEquiv e (comparison p ι hK ρ
          (DirectSum.lof ℂ_[p] ℤ (fun q => ℂ_[p] ⊗[K] localWeightSpace p ι hK ρ q) q x))
      rw [comparisonSourceEquiv_lof, comparison_lof, comparison_lof]
      exact weightComparison_natural p ι hK e q x
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Injectivity of the concrete comparison map is invariant under intertwining equivalence. -/
theorem comparison_injective_iff (e : ρ.Equiv τ) :
    Function.Injective (comparison p ι hK ρ) ↔ Function.Injective (comparison p ι hK τ) := by
  let a := comparisonSourceEquiv p ι hK e
  let b := periodLinearEquiv e
  constructor
  · intro h x y hxy
    obtain ⟨u, rfl⟩ := a.surjective x
    obtain ⟨v, rfl⟩ := a.surjective y
    apply congrArg a
    apply h
    apply b.injective
    rw [← comparison_natural p ι hK e, ← comparison_natural p ι hK e]
    exact hxy
  · intro h x y hxy
    apply a.injective
    apply h
    rw [comparison_natural p ι hK e, comparison_natural p ι hK e, hxy]

/-- Surjectivity of the concrete comparison map is invariant under intertwining equivalence. -/
theorem comparison_surjective_iff (e : ρ.Equiv τ) :
    Function.Surjective (comparison p ι hK ρ) ↔ Function.Surjective (comparison p ι hK τ) := by
  let a := comparisonSourceEquiv p ι hK e
  let b := periodLinearEquiv e
  constructor
  · intro h x
    obtain ⟨y, rfl⟩ := b.surjective x
    obtain ⟨z, hz⟩ := h y
    exact ⟨a z, (comparison_natural p ι hK e z).trans (congrArg b hz)⟩
  · intro h x
    obtain ⟨y, hy⟩ := h (b x)
    obtain ⟨z, rfl⟩ := a.surjective y
    refine ⟨z, b.injective ?_⟩
    rw [← comparison_natural p ι hK e]
    exact hy

/-- Bijectivity of the actual comparison map is preserved under intertwining equivalence. -/
theorem comparison_bijective_iff (e : ρ.Equiv τ) :
    Function.Bijective (comparison p ι hK ρ) ↔ Function.Bijective (comparison p ι hK τ) :=
  and_congr (comparison_injective_iff p ι hK e) (comparison_surjective_iff p ι hK e)

/-- Intertwining equivalences preserve the dimensions of the local-base-field weight spaces. -/
theorem finrank_localWeightSpace_eq (e : ρ.Equiv τ) (q : ℤ) :
    Module.finrank K (localWeightSpace p ι hK ρ q) =
      Module.finrank K (localWeightSpace p ι hK τ q) :=
  (localWeightSpaceEquiv p ι hK e q).finrank_eq

end Equivalences

section CoefficientConjugation

variable {E : Type*} [Field E] [Algebra ℚ_[p] E]
  (σ : E ≃ₐ[ℚ_[p]] E) (A : Rep E G)
  [Module ℚ_[p] A] [IsScalarTower ℚ_[p] E A]
  [Module ℚ_[p] (Rep.scalarConjugate σ.toRingEquiv A)]
  [IsScalarTower ℚ_[p] E (Rep.scalarConjugate σ.toRingEquiv A)]

/-- Conjugating coefficients preserves bijectivity of the concrete Hodge–Tate comparison map. -/
theorem scalarConjugate_comparison_bijective_iff :
    Function.Bijective (comparison p ι hK (A.ρ.restrictScalars ℚ_[p])) ↔
      Function.Bijective (comparison p ι hK
        ((Rep.scalarConjugate σ.toRingEquiv A).ρ.restrictScalars ℚ_[p])) :=
  comparison_bijective_iff p ι hK (Rep.scalarConjugateRestrictScalarsEquiv ℚ_[p] σ A)

/-- Coefficient conjugation preserves every actual local-base-field period dimension. -/
theorem scalarConjugate_finrank_localWeightSpace (q : ℤ) :
    Module.finrank K (localWeightSpace p ι hK (A.ρ.restrictScalars ℚ_[p]) q) =
      Module.finrank K (localWeightSpace p ι hK
        ((Rep.scalarConjugate σ.toRingEquiv A).ρ.restrictScalars ℚ_[p]) q) :=
  finrank_localWeightSpace_eq p ι hK (Rep.scalarConjugateRestrictScalarsEquiv ℚ_[p] σ A) q

/-- Coefficient conjugation preserves rank-one quotients with bijective actual comparison
and no nonzero-weight periods. This expresses the weight-zero Hodge–Tate condition
using the concrete maps and eigenspaces, without an assigned weight function. -/
theorem scalarConjugate_exists_weight_zero_quotient_iff :
    (∃ S : Subrepresentation A.ρ, Module.finrank E (A ⧸ S.toSubmodule) = 1 ∧
      Function.Bijective (comparison p ι hK
        ((A.ρ.quotient S.toSubmodule S.apply_mem_toSubmodule).restrictScalars ℚ_[p])) ∧
      ∀ q : ℤ, q ≠ 0 → weightSpace p ι
        ((A.ρ.quotient S.toSubmodule S.apply_mem_toSubmodule).restrictScalars ℚ_[p]) q = ⊥) ↔
    ∃ T : Subrepresentation (Rep.scalarConjugate σ.toRingEquiv A).ρ,
      Module.finrank E (Rep.scalarConjugate σ.toRingEquiv A ⧸ T.toSubmodule) = 1 ∧
      Function.Bijective (comparison p ι hK
        (((Rep.scalarConjugate σ.toRingEquiv A).ρ.quotient
          T.toSubmodule T.apply_mem_toSubmodule).restrictScalars ℚ_[p])) ∧
      ∀ q : ℤ, q ≠ 0 → weightSpace p ι
        (((Rep.scalarConjugate σ.toRingEquiv A).ρ.quotient
          T.toSubmodule T.apply_mem_toSubmodule).restrictScalars ℚ_[p]) q = ⊥ := by
  constructor
  · rintro ⟨S, hdim, hcomp, hweights⟩
    refine ⟨Rep.scalarConjugateSubrepresentationEquiv σ.toRingEquiv A S, ?_, ?_, ?_⟩
    · exact (Rep.finrank_scalarConjugate_quotient σ.toRingEquiv A S).trans hdim
    · exact (comparison_bijective_iff p ι hK
        (Rep.scalarConjugateQuotientRestrictScalarsEquiv ℚ_[p] σ A S)).mp hcomp
    · intro q hq
      exact (weightSpace_eq_bot_iff
        (Rep.scalarConjugateQuotientRestrictScalarsEquiv ℚ_[p] σ A S) q).mp (hweights q hq)
  · rintro ⟨T, hdim, hcomp, hweights⟩
    obtain ⟨S, rfl⟩ := (Rep.scalarConjugateSubrepresentationEquiv σ.toRingEquiv A).surjective T
    refine ⟨S, ?_, ?_, ?_⟩
    · exact (Rep.finrank_scalarConjugate_quotient σ.toRingEquiv A S).symm.trans hdim
    · exact (comparison_bijective_iff p ι hK
        (Rep.scalarConjugateQuotientRestrictScalarsEquiv ℚ_[p] σ A S)).mpr hcomp
    · intro q hq
      exact (weightSpace_eq_bot_iff
        (Rep.scalarConjugateQuotientRestrictScalarsEquiv ℚ_[p] σ A S) q).mpr (hweights q hq)

end CoefficientConjugation

end HodgeTate
