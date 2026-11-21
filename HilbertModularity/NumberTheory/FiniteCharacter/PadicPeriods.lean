/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.FiniteCharacter.TensorPeriods
public import HilbertModularity.NumberTheory.PadicGalois
public import HilbertModularity.LinearAlgebra.CoefficientDecomposition

/-! # Actual p-adic periods of finite characters

The algebraic coefficient tensor splits over the algebraic closure of `Q_p`.
Its constructed unit period maps to the actual completed p-adic period tensor,
with the Galois action extended by continuity, as in [TripathiGoswami].
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace PadicComplex

variable (p : ℕ) [Fact p.Prime]

/-- A continuous finite-image rational p-adic character has an actual nonzero `C_p` period. -/
theorem exists_period_of_continuous_finite_range
    (χ : Gal(PadicAlgCl p/ℚ_[p]) →* ℚ_[p]ˣ) (hχ : Continuous χ)
    (hfin : (Set.range χ).Finite) :
    ∃ c : ℂ_[p]ˣ, ∀ g : Gal(PadicAlgCl p/ℚ_[p]),
      galoisEquiv p g (c : ℂ_[p]) * algebraMap ℚ_[p] ℂ_[p] (χ g : ℚ_[p]) = c := by
  obtain ⟨c, hc⟩ := FiniteCharacter.exists_period_of_continuous_finite_range χ hχ hfin
  refine ⟨Units.map (algebraMap (PadicAlgCl p) ℂ_[p]).toMonoidHom c, fun g => ?_⟩
  change galoisEquiv p g ((c : PadicAlgCl p) : ℂ_[p]) *
    algebraMap ℚ_[p] ℂ_[p] (χ g : ℚ_[p]) = ((c : PadicAlgCl p) : ℂ_[p])
  rw [galoisEquiv_coe]
  change algebraMap (PadicAlgCl p) ℂ_[p] (g (c : PadicAlgCl p)) * _ = _
  rw [IsScalarTower.algebraMap_apply ℚ_[p] (PadicAlgCl p) ℂ_[p], ← map_mul, hc]
  rfl

/-- Rational-valued finite characters of an embedded local decomposition group have scalar periods. -/
theorem exists_local_period_of_continuous_finite_range
    {K : Type*} [Field K] [Algebra ℚ_[p] K] [Algebra K (PadicAlgCl p)]
    [IsScalarTower ℚ_[p] K (PadicAlgCl p)]
    (χ : Gal(PadicAlgCl p/K) →* ℚ_[p]ˣ) (hχ : Continuous χ)
    (hfin : (Set.range χ).Finite) :
    ∃ c : ℂ_[p]ˣ, ∀ g : Gal(PadicAlgCl p/K),
      galoisEquiv p (g.restrictScalars ℚ_[p]) (c : ℂ_[p]) *
        algebraMap ℚ_[p] ℂ_[p] (χ g : ℚ_[p]) = c := by
  let : IsGalois K (PadicAlgCl p) := IsGalois.tower_top_of_isGalois ℚ_[p] K (PadicAlgCl p)
  let u : ℚ_[p]ˣ →* Kˣ := Units.map (algebraMap ℚ_[p] K).toMonoidHom
  let ψ : Gal(PadicAlgCl p/K) →* Kˣ := u.comp χ
  have hu : Function.Injective u := Units.map_injective (algebraMap ℚ_[p] K).injective
  have hker : ψ.ker = χ.ker := by
    ext g
    change u (χ g) = 1 ↔ χ g = 1
    rw [← map_one u, hu.eq_iff]
  obtain ⟨c, hc⟩ := FiniteCharacter.exists_period_of_isOpen_ker ψ
    (hker ▸ χ.isOpen_ker_of_finite_range hχ hfin)
  refine ⟨Units.map (algebraMap (PadicAlgCl p) ℂ_[p]).toMonoidHom c, fun g => ?_⟩
  change galoisEquiv p (g.restrictScalars ℚ_[p]) ((c : PadicAlgCl p) : ℂ_[p]) *
    algebraMap ℚ_[p] ℂ_[p] (χ g : ℚ_[p]) = ((c : PadicAlgCl p) : ℂ_[p])
  rw [galoisEquiv_coe]
  have h : g (c : PadicAlgCl p) * algebraMap ℚ_[p] (PadicAlgCl p) (χ g : ℚ_[p]) = c := by
    simpa [ψ, u, ← IsScalarTower.algebraMap_apply ℚ_[p] K (PadicAlgCl p)] using hc g
  change algebraMap (PadicAlgCl p) ℂ_[p] (g (c : PadicAlgCl p)) * _ = _
  rw [IsScalarTower.algebraMap_apply ℚ_[p] (PadicAlgCl p) ℂ_[p], ← map_mul, h]
  rfl

variable {L : Type*} [Field L] [Algebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]

/-- A finite coefficient character has an invertible period in the actual completed tensor. -/
theorem exists_tensor_period_of_continuous_finite_range
    [TopologicalSpace Lˣ] [T1Space Lˣ]
    (χ : Gal(PadicAlgCl p/ℚ_[p]) →* Lˣ) (hχ : Continuous χ)
    (hfin : (Set.range χ).Finite) :
    ∃ c : (ℂ_[p] ⊗[ℚ_[p]] L)ˣ, ∀ g : Gal(PadicAlgCl p/ℚ_[p]),
      Algebra.TensorProduct.map (galoisEquiv p g).toAlgHom (AlgHom.id ℚ_[p] L)
          (c : ℂ_[p] ⊗[ℚ_[p]] L) *
        ((1 : ℂ_[p]) ⊗ₜ[ℚ_[p]] (χ g : L)) = c := by
  let e := Algebra.TensorProduct.embeddingEquiv ℚ_[p] L (PadicAlgCl p)
    (fun _ => IsAlgClosed.splits _)
  exact FiniteCharacter.exists_tensor_period_in_overfield
    (IsScalarTower.toAlgHom ℚ_[p] (PadicAlgCl p) ℂ_[p])
    (fun g => (galoisEquiv p g).toAlgHom) (fun g x => galoisEquiv_coe p g x)
    χ (χ.isOpen_ker_of_finite_range hχ hfin) e
    (Algebra.TensorProduct.embeddingEquiv_tmul ℚ_[p] L (PadicAlgCl p) _)

/-- Tensor periods for the actual decomposition group over any embedded local base field. -/
theorem exists_local_tensor_period_of_continuous_finite_range
    {K : Type*} [Field K] [Algebra ℚ_[p] K] [Algebra K (PadicAlgCl p)]
    [IsScalarTower ℚ_[p] K (PadicAlgCl p)]
    [TopologicalSpace Lˣ] [T1Space Lˣ]
    (χ : Gal(PadicAlgCl p/K) →* Lˣ) (hχ : Continuous χ)
    (hfin : (Set.range χ).Finite) :
    ∃ c : (ℂ_[p] ⊗[ℚ_[p]] L)ˣ, ∀ g : Gal(PadicAlgCl p/K),
      Algebra.TensorProduct.map (galoisEquiv p (g.restrictScalars ℚ_[p])).toAlgHom
          (AlgHom.id ℚ_[p] L) (c : ℂ_[p] ⊗[ℚ_[p]] L) *
        ((1 : ℂ_[p]) ⊗ₜ[ℚ_[p]] (χ g : L)) = c := by
  let : IsGalois K (PadicAlgCl p) := IsGalois.tower_top_of_isGalois ℚ_[p] K (PadicAlgCl p)
  let e := Algebra.TensorProduct.embeddingEquiv ℚ_[p] L (PadicAlgCl p)
    (fun _ => IsAlgClosed.splits _)
  exact FiniteCharacter.exists_tensor_period_in_overfield (K := K)
    (IsScalarTower.toAlgHom ℚ_[p] (PadicAlgCl p) ℂ_[p])
    (fun g => (galoisEquiv p (g.restrictScalars ℚ_[p])).toAlgHom)
    (fun g x => galoisEquiv_coe p (g.restrictScalars ℚ_[p]) x)
    χ (χ.isOpen_ker_of_finite_range hχ hfin) e
    (Algebra.TensorProduct.embeddingEquiv_tmul ℚ_[p] L (PadicAlgCl p) _)

/-- Finite order gives actual local tensor periods without a separate finite-image hypothesis. -/
theorem exists_local_tensor_period_of_continuous_pow_eq_one
    {K : Type*} [Field K] [Algebra ℚ_[p] K] [Algebra K (PadicAlgCl p)]
    [IsScalarTower ℚ_[p] K (PadicAlgCl p)]
    [TopologicalSpace Lˣ] [T1Space Lˣ]
    (χ : Gal(PadicAlgCl p/K) →* Lˣ) (hχ : Continuous χ)
    {n : ℕ} (hn : n ≠ 0) (hpow : ∀ g, χ g ^ n = 1) :
    ∃ c : (ℂ_[p] ⊗[ℚ_[p]] L)ˣ, ∀ g : Gal(PadicAlgCl p/K),
      Algebra.TensorProduct.map (galoisEquiv p (g.restrictScalars ℚ_[p])).toAlgHom
          (AlgHom.id ℚ_[p] L) (c : ℂ_[p] ⊗[ℚ_[p]] L) *
        ((1 : ℂ_[p]) ⊗ₜ[ℚ_[p]] (χ g : L)) = c :=
  exists_local_tensor_period_of_continuous_finite_range p χ hχ
    (χ.finite_range_of_pow_eq_one hn hpow)

/-- A continuous finite-order local character has an actual invertible completed tensor period. -/
theorem exists_local_tensor_period_of_continuous_isOfFinOrder
    {K : Type*} [Field K] [Algebra ℚ_[p] K] [Algebra K (PadicAlgCl p)]
    [IsScalarTower ℚ_[p] K (PadicAlgCl p)]
    [TopologicalSpace Lˣ] [T1Space Lˣ]
    (χ : Gal(PadicAlgCl p/K) →* Lˣ) (hχ : Continuous χ) (horder : IsOfFinOrder χ) :
    ∃ c : (ℂ_[p] ⊗[ℚ_[p]] L)ˣ, ∀ g : Gal(PadicAlgCl p/K),
      Algebra.TensorProduct.map (galoisEquiv p (g.restrictScalars ℚ_[p])).toAlgHom
          (AlgHom.id ℚ_[p] L) (c : ℂ_[p] ⊗[ℚ_[p]] L) *
        ((1 : ℂ_[p]) ⊗ₜ[ℚ_[p]] (χ g : L)) = c :=
  exists_local_tensor_period_of_continuous_finite_range p χ hχ
    (χ.finite_range_of_isOfFinOrder horder)

end PadicComplex
