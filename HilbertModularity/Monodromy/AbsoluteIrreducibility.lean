/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Monodromy.Rigidity
public import HilbertModularity.RepresentationTheory.ScalarExtension
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.Tactic.Module

/-! # Absolute irreducibility from two unipotent cusps

The simultaneous transvection basis in [TripathiGoswami, rigid triple lemma]
forces every nonzero invariant subspace to contain both basis vectors. The
argument survives arbitrary extension of the coefficient field.
-/

@[expose] public noncomputable section

open scoped TensorProduct Matrix

namespace Module.Basis

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- A nonzero subspace stable under two transverse transvections is the whole space. -/
theorem submodule_eq_top_of_transvections (b : Basis (Fin 2) K V)
    (A B : Module.End K V) (t : K) (ht : t ≠ 0)
    (hA0 : A (b 0) = b 0) (hA1 : A (b 1) = b 0 + b 1)
    (hB0 : B (b 0) = b 0 + t • b 1)
    (S : Submodule K V) (hS : S ≠ ⊥)
    (hAS : ∀ v ∈ S, A v ∈ S) (hBS : ∀ v ∈ S, B v ∈ S) : S = ⊤ := by
  obtain ⟨v, hv, hvne⟩ : ∃ v, v ∈ S ∧ v ≠ 0 := by
    by_contra! h
    apply hS
    apply bot_unique
    intro v hv
    exact h v hv
  have hvrepr : v = b.repr v 0 • b 0 + b.repr v 1 • b 1 := by
    simpa only [Fin.sum_univ_two] using (b.sum_repr v).symm
  have hb0 : b 0 ∈ S := by
    by_cases h1 : b.repr v 1 = 0
    · have h0 : b.repr v 0 ≠ 0 := by
        intro h0
        apply hvne
        simp [h0, h1] at hvrepr
        exact hvrepr
      have hm : b.repr v 0 • b 0 ∈ S := by
        have hv' : b.repr v 0 • b 0 + b.repr v 1 • b 1 ∈ S := by
          rw [← hvrepr]
          exact hv
        simpa only [h1, zero_smul, add_zero] using hv'
      simpa only [smul_smul, inv_mul_cancel₀ h0, one_smul] using
        S.smul_mem (b.repr v 0)⁻¹ hm
    · have he : A v - v = b.repr v 1 • b 0 := by
        calc
          A v - v = A (b.repr v 0 • b 0 + b.repr v 1 • b 1) -
              (b.repr v 0 • b 0 + b.repr v 1 • b 1) :=
            congrArg (fun w => A w - w) hvrepr
          _ = _ := by
            simp only [map_add, map_smul, hA0, hA1]
            module
      have hm : b.repr v 1 • b 0 ∈ S := he ▸ S.sub_mem (hAS v hv) hv
      simpa only [smul_smul, inv_mul_cancel₀ h1, one_smul] using
        S.smul_mem (b.repr v 1)⁻¹ hm
  have hb1 : b 1 ∈ S := by
    have hm : t • b 1 ∈ S := by
      have h := S.sub_mem (hBS (b 0) hb0) hb0
      simpa only [hB0, add_sub_cancel_left] using h
    simpa only [smul_smul, inv_mul_cancel₀ ht, one_smul] using S.smul_mem t⁻¹ hm
  apply top_unique
  intro w _
  rw [← b.sum_repr w, Fin.sum_univ_two]
  exact S.add_mem (S.smul_mem _ hb0) (S.smul_mem _ hb1)

end Module.Basis

namespace Representation

variable {K G V : Type*} [Field K] [Monoid G] [AddCommGroup V] [Module K V]

/-- A representation containing two transverse transvections is irreducible. -/
theorem isIrreducible_of_transvection_basis (ρ : Representation K G V)
    (b : Module.Basis (Fin 2) K V) (a c : G) (t : K) (ht : t ≠ 0)
    (hA0 : ρ a (b 0) = b 0) (hA1 : ρ a (b 1) = b 0 + b 1)
    (hB0 : ρ c (b 0) = b 0 + t • b 1) : ρ.IsIrreducible := by
  let : Nontrivial (Subrepresentation ρ) := ⟨⟨⊥, ⊤, by
    intro h
    have hm : b 0 ∈ (⊥ : Subrepresentation ρ) := by rw [h]; trivial
    exact b.ne_zero 0 hm⟩⟩
  apply IsSimpleOrder.of_forall_eq_top
  intro S hS
  apply Subrepresentation.toSubmodule_injective
  apply b.submodule_eq_top_of_transvections (ρ a) (ρ c) t ht hA0 hA1 hB0
  · intro h
    exact hS (Subrepresentation.toSubmodule_injective h)
  · exact fun v hv => S.apply_mem_toSubmodule a hv
  · exact fun v hv => S.apply_mem_toSubmodule c hv

/-- The transverse-transvection criterion is preserved by every coefficient extension. -/
theorem isIrreducible_baseChange_of_transvection_basis
    (E : Type*) [Field E] [Algebra K E] (ρ : Representation K G V)
    (b : Module.Basis (Fin 2) K V) (a c : G) (t : K) (ht : t ≠ 0)
    (hA0 : ρ a (b 0) = b 0) (hA1 : ρ a (b 1) = b 0 + b 1)
    (hB0 : ρ c (b 0) = b 0 + t • b 1) : (ρ.baseChange E).IsIrreducible := by
  apply isIrreducible_of_transvection_basis (ρ.baseChange E) (b.baseChange E)
    a c (algebraMap K E t) ((map_ne_zero _).mpr ht)
  · simp only [Module.Basis.baseChange_apply, baseChange_tmul, hA0]
  · simp only [Module.Basis.baseChange_apply, baseChange_tmul, hA1, TensorProduct.tmul_add]
  · simp only [Module.Basis.baseChange_apply, baseChange_tmul, hB0, TensorProduct.tmul_add]
    simp only [baseChange_balance, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

end Representation

namespace Representation

/-- Two transverse transvections over a coefficient ring remain irreducible
after specialization to a field, provided their transverse parameter survives. -/
theorem isIrreducible_specialization_of_transvection_basis
    {R G V : Type*} [CommRing R] [Monoid G] [AddCommGroup V] [Module R V]
    (E : Type*) [Field E] [Algebra R E] (ρ : Representation R G V)
    (b : Module.Basis (Fin 2) R V) (a c : G) (t : R)
    (ht : algebraMap R E t ≠ 0)
    (hA0 : ρ a (b 0) = b 0) (hA1 : ρ a (b 1) = b 0 + b 1)
    (hB0 : ρ c (b 0) = b 0 + t • b 1) : (ρ.baseChange E).IsIrreducible := by
  apply isIrreducible_of_transvection_basis (ρ.baseChange E) (b.baseChange E)
    a c (algebraMap R E t) ht
  · simp only [Module.Basis.baseChange_apply, baseChange_tmul, hA0]
  · simp only [Module.Basis.baseChange_apply, baseChange_tmul, hA1, TensorProduct.tmul_add]
  · simp only [Module.Basis.baseChange_apply, baseChange_tmul, hB0, TensorProduct.tmul_add]
    simp only [baseChange_balance, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

end Representation

namespace HilbertModularity.Monodromy

/-- The two finite cusps of the standard triple force irreducibility after a
field specialization for which the trace parameter is not two. -/
theorem isIrreducible_specialization_of_standard_cusps
    {R G V : Type*} [CommRing R] [Monoid G] [AddCommGroup V] [Module R V]
    (E : Type*) [Field E] [Algebra R E] (ρ : Representation R G V)
    (b : Module.Basis (Fin 2) R V) (a c : G) (τ : R)
    (hτ : algebraMap R E τ ≠ 2)
    (h0 : ∀ v, (b.repr (ρ a v) : Fin 2 → R) = U0 *ᵥ b.repr v)
    (h1 : ∀ v, (b.repr (ρ c v) : Fin 2 → R) = U1 τ *ᵥ b.repr v) :
    (ρ.baseChange E).IsIrreducible := by
  apply Representation.isIrreducible_specialization_of_transvection_basis E ρ b a c
    (τ - 2) (by simpa only [map_sub, map_ofNat] using sub_ne_zero.mpr hτ)
  · apply b.repr.injective
    ext i
    have h := congrFun (h0 (b 0)) i
    fin_cases i <;> simpa [U0, Matrix.mulVec, Fin.sum_univ_two, Matrix.vecHead, Matrix.vecTail] using h
  · apply b.repr.injective
    ext i
    have h := congrFun (h0 (b 1)) i
    fin_cases i <;> simpa [U0, Matrix.mulVec, Fin.sum_univ_two, Matrix.vecHead, Matrix.vecTail] using h
  · apply b.repr.injective
    ext i
    have h := congrFun (h1 (b 0)) i
    fin_cases i <;> simpa [U1, Matrix.mulVec, Fin.sum_univ_two, Matrix.vecHead, Matrix.vecTail] using h

/-- A rank-two representation with two nontrivial unipotent cusps and no common
fixed vector is irreducible after every extension of its coefficient field. -/
theorem isIrreducible_baseChange_of_unipotent_cusps
    {K G : Type*} [Field K] [Monoid G] (E : Type*) [Field E] [Algebra K E]
    (ρ : Representation K G (Fin 2 → K)) (a c : G)
    (hA : (ρ a - 1) ^ 2 = 0) (hB : (ρ c - 1) ^ 2 = 0) (hBne : ρ c ≠ 1)
    (hirr : ∀ v, ρ a v = v → ρ c v = v → v = 0) :
    (ρ.baseChange E).IsIrreducible := by
  obtain ⟨b, τ, hτ, h0, h1⟩ := exists_basis_unipotent_pair
    (ρ a) (ρ c) hA hB hBne hirr
  apply Representation.isIrreducible_baseChange_of_transvection_basis E ρ b a c
    (τ - 2) (sub_ne_zero.mpr hτ)
  · apply b.repr.injective
    ext i
    have h := congrArg (fun M => M i 0) h0
    fin_cases i <;> simpa [LinearMap.toMatrix_apply, U0] using h
  · apply b.repr.injective
    ext i
    have h := congrArg (fun M => M i 1) h0
    fin_cases i <;> simpa [LinearMap.toMatrix_apply, U0] using h
  · apply b.repr.injective
    ext i
    have h := congrArg (fun M => M i 0) h1
    fin_cases i <;> simpa [LinearMap.toMatrix_apply, U1] using h

end HilbertModularity.Monodromy
