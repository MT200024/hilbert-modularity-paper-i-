/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.HodgeTateComparison
public import Mathlib.RingTheory.Flat.Basic

/-! # Functoriality of the Hodge–Tate comparison

An actual equivariant linear map induces maps on cyclotomic period spaces and
on the source of the canonical comparison. Injective maps preserve injectivity
of the comparison by flatness over the local base field.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace HodgeTate

variable (p : ℕ) [Fact p.Prime]
  {G : Type*} [Group G]
  (ι : G →* (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p))
  {K : Type*} [Field K] [Algebra ℚ_[p] K] [Algebra K ℂ_[p]]
  [IsScalarTower ℚ_[p] K ℂ_[p]]
  (hK : ∀ (g : G) (a : K), PadicComplex.galoisEquiv p (ι g)
    (algebraMap K ℂ_[p] a) = algebraMap K ℂ_[p] a)
  {V W : Type*} [AddCommGroup V] [Module ℚ_[p] V]
  [AddCommGroup W] [Module ℚ_[p] W]
  {ρ : Representation ℚ_[p] G V} {τ : Representation ℚ_[p] G W}

/-- The map on local-base-field weight spaces induced by an intertwining map. -/
def localWeightSpaceMap (f : ρ.IntertwiningMap τ) (q : ℤ) :
    localWeightSpace p ι hK ρ q →ₗ[K] localWeightSpace p ι hK τ q :=
  (((periodLinearMap f).restrictScalars K).comp
    (localWeightSpace p ι hK ρ q).subtype).codRestrict _ (by
      intro x
      exact periodLinearMap_mem_weightSpace f q x x.property)

/-- The scalar extension of the induced map on one weight space. -/
def weightComparisonSourceMap (f : ρ.IntertwiningMap τ) (q : ℤ) :
    (ℂ_[p] ⊗[K] localWeightSpace p ι hK ρ q) →ₗ[ℂ_[p]]
      ℂ_[p] ⊗[K] localWeightSpace p ι hK τ q :=
  TensorProduct.AlgebraTensorModule.lTensor ℂ_[p] ℂ_[p] (localWeightSpaceMap p ι hK f q)

/-- The one-weight comparison commutes with every intertwining map. -/
theorem weightComparison_map (f : ρ.IntertwiningMap τ) (q : ℤ)
    (x : ℂ_[p] ⊗[K] localWeightSpace p ι hK ρ q) :
    weightComparison p ι hK τ q (weightComparisonSourceMap p ι hK f q x) =
      periodLinearMap f (weightComparison p ι hK ρ q x) := by
  induction x using TensorProduct.inductionOn with
  | tmul c x => exact ((periodLinearMap f).map_smul c x).symm
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The map on the entire comparison source induced by an intertwining map. -/
def comparisonSourceMap (f : ρ.IntertwiningMap τ) :
    (DirectSum ℤ (fun q => ℂ_[p] ⊗[K] localWeightSpace p ι hK ρ q)) →ₗ[ℂ_[p]]
      DirectSum ℤ (fun q => ℂ_[p] ⊗[K] localWeightSpace p ι hK τ q) :=
  DirectSum.lmap (weightComparisonSourceMap p ι hK f)

/-- The canonical comparison commutes with every intertwining map. -/
theorem comparison_map (f : ρ.IntertwiningMap τ)
    (x : DirectSum ℤ (fun q => ℂ_[p] ⊗[K] localWeightSpace p ι hK ρ q)) :
    comparison p ι hK τ (comparisonSourceMap p ι hK f x) =
      periodLinearMap f (comparison p ι hK ρ x) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of q x =>
      change comparison p ι hK τ (comparisonSourceMap p ι hK f
        (DirectSum.lof ℂ_[p] ℤ (fun q => ℂ_[p] ⊗[K] localWeightSpace p ι hK ρ q) q x)) =
        periodLinearMap f (comparison p ι hK ρ
          (DirectSum.lof ℂ_[p] ℤ (fun q => ℂ_[p] ⊗[K] localWeightSpace p ι hK ρ q) q x))
      simp only [comparisonSourceMap, DirectSum.lmap_lof, comparison_lof]
      exact weightComparison_map p ι hK f q x
  | add x y hx hy => simp only [map_add, hx, hy]

/-- An injective intertwiner induces an injective map on every weight space. -/
theorem localWeightSpaceMap_injective (f : ρ.IntertwiningMap τ)
    (hf : Function.Injective f) (q : ℤ) :
    Function.Injective (localWeightSpaceMap p ι hK f q) := by
  intro x y hxy
  apply Subtype.ext
  apply Module.Flat.lTensor_preserves_injective_linearMap f.toLinearMap hf
  exact congrArg Subtype.val hxy

/-- An injective intertwiner induces an injective map on the comparison source. -/
theorem comparisonSourceMap_injective (f : ρ.IntertwiningMap τ)
    (hf : Function.Injective f) : Function.Injective (comparisonSourceMap p ι hK f) := by
  apply (DirectSum.lmap_injective _).mpr
  intro q
  exact Module.Flat.lTensor_preserves_injective_linearMap
    (localWeightSpaceMap p ι hK f q) (localWeightSpaceMap_injective p ι hK f hf q)

/-- Comparison injectivity descends along an injective equivariant linear map. -/
theorem comparison_injective_of_injective (f : ρ.IntertwiningMap τ)
    (hf : Function.Injective f) (hτ : Function.Injective (comparison p ι hK τ)) :
    Function.Injective (comparison p ι hK ρ) := by
  intro x y hxy
  apply comparisonSourceMap_injective p ι hK f hf
  apply hτ
  rw [comparison_map, comparison_map, hxy]

section PeriodEquivalences

variable (e : (ℂ_[p] ⊗[ℚ_[p]] V) ≃ₗ[ℂ_[p]] (ℂ_[p] ⊗[ℚ_[p]] W))
  (he : ∀ (g : G) (x : ℂ_[p] ⊗[ℚ_[p]] V),
    e (periodRepresentation p ι ρ g x) = periodRepresentation p ι τ g (e x))

include he

/-- A `Cp`-linear intertwiner of actual period actions preserves every cyclotomic weight. -/
theorem periodLinearEquiv_mem_weightSpace_iff (q : ℤ) (x : ℂ_[p] ⊗[ℚ_[p]] V) :
    e x ∈ weightSpace p ι τ q ↔ x ∈ weightSpace p ι ρ q := by
  simp only [mem_weightSpace]
  apply forall_congr'
  intro g
  have hs (a : ℚ_[p]) : e (a • x) = a • e x :=
    e.toLinearMap.map_smul_of_tower a x
  rw [← he g x, ← hs]
  exact e.injective.eq_iff

/-- An actual period-action equivalence identifies the local-base-field weight spaces. -/
def localWeightSpacePeriodEquiv (q : ℤ) :
    localWeightSpace p ι hK ρ q ≃ₗ[K] localWeightSpace p ι hK τ q :=
  (e.restrictScalars K).ofSubmodules _ _ (by
    ext y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨z, hz, hzx⟩
      have h : z = x := e.injective hzx
      exact (periodLinearEquiv_mem_weightSpace_iff p ι e he q x).mpr (h ▸ hz)
    · intro hx
      exact ⟨x, (periodLinearEquiv_mem_weightSpace_iff p ι e he q x).mp hx, rfl⟩)

/-- An actual period-action equivalence identifies the full comparison sources. -/
def comparisonSourcePeriodEquiv :
    (DirectSum ℤ (fun q => ℂ_[p] ⊗[K] localWeightSpace p ι hK ρ q)) ≃ₗ[ℂ_[p]]
      DirectSum ℤ (fun q => ℂ_[p] ⊗[K] localWeightSpace p ι hK τ q) :=
  DirectSum.congrLinearEquiv (fun q =>
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl ℂ_[p] ℂ_[p])
      (localWeightSpacePeriodEquiv p ι hK e he q))

/-- Comparison is natural for `Cp`-linear equivalences of the actual period actions. -/
theorem comparison_periodEquiv
    (x : DirectSum ℤ (fun q => ℂ_[p] ⊗[K] localWeightSpace p ι hK ρ q)) :
    comparison p ι hK τ (comparisonSourcePeriodEquiv p ι hK e he x) =
      e (comparison p ι hK ρ x) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of q x =>
      change comparison p ι hK τ (comparisonSourcePeriodEquiv p ι hK e he
        (DirectSum.lof ℂ_[p] ℤ (fun q => ℂ_[p] ⊗[K] localWeightSpace p ι hK ρ q) q x)) =
        e (comparison p ι hK ρ
          (DirectSum.lof ℂ_[p] ℤ (fun q => ℂ_[p] ⊗[K] localWeightSpace p ι hK ρ q) q x))
      simp only [comparisonSourcePeriodEquiv, DirectSum.coe_congrLinearEquiv,
        DirectSum.lmap_lof, comparison_lof]
      induction x using TensorProduct.inductionOn with
      | tmul c x => exact (e.map_smul c x).symm
      | add x y hx hy => simp only [map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Bijectivity of comparison is preserved by an actual `Cp`-linear period-action equivalence. -/
theorem comparison_bijective_periodEquiv_iff :
    Function.Bijective (comparison p ι hK ρ) ↔ Function.Bijective (comparison p ι hK τ) := by
  let a := comparisonSourcePeriodEquiv p ι hK e he
  have h : comparison p ι hK τ ∘ a = e ∘ comparison p ι hK ρ :=
    funext (comparison_periodEquiv p ι hK e he)
  rw [← Function.Bijective.of_comp_iff' e.bijective, ← h,
    Function.Bijective.of_comp_iff _ a.bijective]

end PeriodEquivalences

section CoefficientExtension

variable {E L : Type*} [Field E] [Field L]
  [Algebra ℚ_[p] E] [Algebra E L] [Algebra ℚ_[p] L]
  [IsScalarTower ℚ_[p] E L] [Module E V] [IsScalarTower ℚ_[p] E V]

/-- Comparison injectivity descends along an arbitrary coefficient-field extension. -/
theorem comparison_injective_of_baseChange (ρ : Representation E G V)
    (hL : Function.Injective (comparison p ι hK ((ρ.baseChange L).restrictScalars ℚ_[p]))) :
    Function.Injective (comparison p ι hK (ρ.restrictScalars ℚ_[p])) := by
  let f : (ρ.restrictScalars ℚ_[p]).IntertwiningMap
      ((ρ.baseChange L).restrictScalars ℚ_[p]) :=
    (Representation.baseChangeTensorMap ρ (1 : L)).restrictScalars ℚ_[p]
  apply comparison_injective_of_injective p ι hK f _ hL
  exact Module.Flat.tensorProduct_mk_injective (R := E) (S := L) (M := V)

end CoefficientExtension

end HodgeTate
