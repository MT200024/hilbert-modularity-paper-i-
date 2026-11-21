/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.AdicCompletion
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.RingTheory.TensorProduct.Maps

/-! # The `p`-adic scalar field of a number-field completion

For a prime above `p`, the canonical map from the rational `p`-adic field to
the corresponding number-field completion extends the rational embedding.
-/

@[expose] public noncomputable section

open IsDedekindDomain
open scoped NumberField

namespace Padic

variable (p : ℕ) [Fact p.Prime]

/-- The rational prime corresponding to `p` has ideal `(p)` in `Z`. -/
@[simp] theorem primesEquiv_symm_asIdeal :
    ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm ⟨p, Fact.out⟩).asIdeal =
      Ideal.span {(p : ℤ)} := by
  let v := (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm ⟨p, Fact.out⟩
  have hn : Rat.HeightOneSpectrum.natGenerator v = p :=
    congrArg Subtype.val (Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply ⟨p, Fact.out⟩)
  have hs := Rat.HeightOneSpectrum.span_natGenerator v
  rw [hn] at hs
  have he : Rat.IsIntegralClosure.intEquiv ℤ = RingEquiv.refl ℤ := by
    ext x
    exact map_intCast (Rat.IsIntegralClosure.intEquiv ℤ) x
  rw [he] at hs
  change Ideal.span {(p : ℤ)} = Ideal.map (RingHom.id ℤ) v.asIdeal at hs
  rw [Ideal.map_id] at hs
  exact hs.symm

end Padic

namespace NumberField

variable (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K]
variable (w : HeightOneSpectrum (𝓞 K)) [w.asIdeal.LiesOver (Ideal.span {(p : ℤ)})]

/-- The canonical embedding of the rational `p`-adic field into a completion above `p`. -/
def padicCompletionMap : ℚ_[p] →+* w.adicCompletion K := by
  let v := (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm ⟨p, Fact.out⟩
  have : w.asIdeal.LiesOver v.asIdeal := by
    simpa only [v, Padic.primesEquiv_symm_asIdeal] using
      (inferInstance : w.asIdeal.LiesOver (Ideal.span {(p : ℤ)}))
  exact (v.completionMap (K := ℚ) (L := K) w).comp
    (Padic.adicCompletionEquiv ℤ ⟨p, Fact.out⟩).toAlgEquiv.toRingEquiv.toRingHom

/-- The canonical `p`-adic embedding is continuous. -/
theorem continuous_padicCompletionMap : Continuous (padicCompletionMap p K w) := by
  let v := (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm ⟨p, Fact.out⟩
  have : w.asIdeal.LiesOver v.asIdeal := by
    simpa only [v, Padic.primesEquiv_symm_asIdeal] using
      (inferInstance : w.asIdeal.LiesOver (Ideal.span {(p : ℤ)}))
  exact (v.continuous_completionMap (K := ℚ) (L := K) w).comp
    (Padic.adicCompletionEquiv ℤ ⟨p, Fact.out⟩).continuous

/-- The canonical `p`-adic scalar action on the completion. -/
instance padicCompletionAlgebra : Algebra ℚ_[p] (w.adicCompletion K) :=
  (padicCompletionMap p K w).toAlgebra

/-- The rational and `p`-adic scalar actions agree. -/
instance padicCompletionIsScalarTower : IsScalarTower ℚ ℚ_[p] (w.adicCompletion K) :=
  IsScalarTower.of_algebraMap_eq fun q => by
    change algebraMap ℚ (w.adicCompletion K) q =
      padicCompletionMap p K w (algebraMap ℚ ℚ_[p] q)
    simp

/-- The action of `Q_p` on a completion above `p` is jointly continuous. -/
instance padicCompletionContinuousSMul : ContinuousSMul ℚ_[p] (w.adicCompletion K) where
  continuous_smul := by
    change Continuous (fun x : ℚ_[p] × w.adicCompletion K => padicCompletionMap p K w x.1 * x.2)
    exact ((continuous_padicCompletionMap p K w).comp continuous_fst).mul continuous_snd

open scoped TensorProduct

/-- The natural scalar-extension map onto a number-field completion above `p`. -/
def padicCompletionTensorMap : ℚ_[p] ⊗[ℚ] K →ₐ[ℚ_[p]] w.adicCompletion K :=
  AlgHom.liftEquiv ℚ ℚ_[p] K (w.adicCompletion K) (Algebra.algHom ℚ K (w.adicCompletion K))

@[simp] theorem padicCompletionTensorMap_tmul (a : ℚ_[p]) (x : K) :
    padicCompletionTensorMap p K w (a ⊗ₜ[ℚ] x) =
      a • algebraMap K (w.adicCompletion K) x := rfl

/-- Density of the number field and closedness of a finite-dimensional image
make the natural map onto its completion surjective. -/
theorem padicCompletionTensorMap_surjective :
    Function.Surjective (padicCompletionTensorMap p K w) := by
  let f := (padicCompletionTensorMap p K w).toLinearMap
  have hd : DenseRange f := by
    apply (w.denseRange_algebraMap K).mono
    rintro _ ⟨x, rfl⟩
    exact ⟨1 ⊗ₜ[ℚ] x, by simp [f]⟩
  change Function.Surjective f
  rw [← Set.range_eq_univ, ← f.coe_range, ← f.range.closed_of_finiteDimensional.closure_eq]
  exact hd.closure_range

/-- A number-field completion above `p` is finite-dimensional over `Q_p`. -/
instance padicCompletionFiniteDimensional : Module.Finite ℚ_[p] (w.adicCompletion K) :=
  Module.Finite.of_surjective (padicCompletionTensorMap p K w).toLinearMap
    (padicCompletionTensorMap_surjective p K w)

/-- If the coefficient tensor is a field, the natural map identifies it with
the completion at every prime above `p`. -/
def padicCompletionTensorEquiv (h : IsField (ℚ_[p] ⊗[ℚ] K)) :
    ℚ_[p] ⊗[ℚ] K ≃ₐ[ℚ_[p]] w.adicCompletion K := by
  letI := h.toField
  exact AlgEquiv.ofBijective (padicCompletionTensorMap p K w)
    ⟨(padicCompletionTensorMap p K w).injective, padicCompletionTensorMap_surjective p K w⟩

@[simp] theorem padicCompletionTensorEquiv_tmul (h : IsField (ℚ_[p] ⊗[ℚ] K))
    (a : ℚ_[p]) (x : K) :
    padicCompletionTensorEquiv p K w h (a ⊗ₜ[ℚ] x) =
      a • algebraMap K (w.adicCompletion K) x := rfl

/-- When the coefficient tensor is a field, every global automorphism extends
canonically to the completion by scalar extension. -/
def padicCompletionAutomorphism (h : IsField (ℚ_[p] ⊗[ℚ] K)) (σ : K ≃ₐ[ℚ] K) :
    w.adicCompletion K ≃ₐ[ℚ_[p]] w.adicCompletion K :=
  (padicCompletionTensorEquiv p K w h).symm.trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : ℚ_[p] ≃ₐ[ℚ_[p]] ℚ_[p]) σ).trans
      (padicCompletionTensorEquiv p K w h))

/-- The completion automorphism extends the prescribed automorphism on the number field. -/
@[simp] theorem padicCompletionAutomorphism_algebraMap (h : IsField (ℚ_[p] ⊗[ℚ] K))
    (σ : K ≃ₐ[ℚ] K) (x : K) :
    padicCompletionAutomorphism p K w h σ (algebraMap K (w.adicCompletion K) x) =
      algebraMap K (w.adicCompletion K) (σ x) := by
  have hx : padicCompletionTensorEquiv p K w h (1 ⊗ₜ[ℚ] x) =
      algebraMap K (w.adicCompletion K) x := by simp
  change padicCompletionTensorEquiv p K w h
    (Algebra.TensorProduct.congr (AlgEquiv.refl : ℚ_[p] ≃ₐ[ℚ_[p]] ℚ_[p]) σ
      ((padicCompletionTensorEquiv p K w h).symm
        (algebraMap K (w.adicCompletion K) x))) = _
  rw [← hx, AlgEquiv.symm_apply_apply]
  simp [Algebra.TensorProduct.congr_apply]

/-- Every extended coefficient automorphism is continuous. -/
theorem continuous_padicCompletionAutomorphism (h : IsField (ℚ_[p] ⊗[ℚ] K))
    (σ : K ≃ₐ[ℚ] K) : Continuous (padicCompletionAutomorphism p K w h σ) :=
  (padicCompletionAutomorphism p K w h σ).toLinearMap.continuous_of_finiteDimensional

end NumberField

namespace NumberField
open IsDedekindDomain
open scoped NumberField
variable (p : ℕ) [Fact p.Prime] (E : Type*) [Field E] [NumberField E]
  (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver (Ideal.span {(p : ℤ)})]
  (L : Type*) [Field L] [TopologicalSpace L]
  [Algebra (w.adicCompletion E) L] [ContinuousSMul (w.adicCompletion E) L]
  [Algebra ℚ_[p] L] [IsScalarTower ℚ_[p] (w.adicCompletion E) L]

include w in
/-- A continuous extension of a coefficient completion has its canonical continuous p-adic scalar action. -/
theorem padicCompletionExtensionContinuousSMul : ContinuousSMul ℚ_[p] L := ⟨by
  have h := ((continuous_algebraMap ℚ_[p] (w.adicCompletion E)).comp
    (continuous_fst : Continuous (fun z : ℚ_[p] × L => z.1))).smul continuous_snd
  change Continuous (fun z : ℚ_[p] × L => algebraMap ℚ_[p] (w.adicCompletion E) z.1 • z.2) at h
  apply h.congr
  intro z
  exact IsScalarTower.algebraMap_smul (w.adicCompletion E) z.1 z.2⟩

end NumberField
