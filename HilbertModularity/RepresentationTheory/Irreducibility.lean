/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.ScalarExtension
public import HilbertModularity.LinearAlgebra.Involution
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Tactic.Module

/-! # Absolute irreducibility from a split involution

A rank-two irreducible representation containing an involution of determinant
minus one remains irreducible after every field extension. We follow the
argument in [TripathiGoswami, proof of absolute irreducibility].
-/

@[expose] public section

open scoped TensorProduct

namespace Module.Basis

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- A nonzero invariant subspace contains an eigenbasis vector of a split
rank-two involution, in characteristic different from two. -/
theorem exists_mem_of_involution (b : Basis (Fin 2) K V) (hK : (2 : K) ≠ 0)
    (f : Module.End K V) (h0 : f (b 0) = b 0) (h1 : f (b 1) = -b 1)
    (S : Submodule K V) (hS : S ≠ ⊥) (hf : ∀ w ∈ S, f w ∈ S) :
    ∃ i, b i ∈ S := by
  obtain ⟨w, hwS, hw⟩ := S.ne_bot_iff.mp hS
  have hr : b.repr w 0 • b 0 + b.repr w 1 • b 1 = w := by
    simpa only [Fin.sum_univ_two] using b.sum_repr w
  by_cases ha : b.repr w 0 = 0
  · have hb : b.repr w 1 ≠ 0 := by
      intro hb
      apply hw
      rw [← hr, ha, hb]
      simp
    refine ⟨1, ?_⟩
    have hp : w - f w = (2 * b.repr w 1) • b 1 := by
      conv_lhs => rw [← hr]
      rw [map_add, map_smul, map_smul, h0, h1]
      module
    have hm := S.sub_mem hwS (hf w hwS)
    rw [hp] at hm
    have h := S.smul_mem (2 * b.repr w 1)⁻¹ hm
    simpa only [smul_smul, inv_mul_cancel₀ (mul_ne_zero hK hb), one_smul] using h
  · refine ⟨0, ?_⟩
    have hp : f w + w = (2 * b.repr w 0) • b 0 := by
      conv_lhs => rw [← hr]
      rw [map_add, map_smul, map_smul, h0, h1]
      module
    have hm := S.add_mem (hf w hwS) hwS
    rw [hp] at hm
    have h := S.smul_mem (2 * b.repr w 0)⁻¹ hm
    simpa only [smul_smul, inv_mul_cancel₀ (mul_ne_zero hK ha), one_smul] using h

end Module.Basis

namespace Representation

variable {K E G V : Type*} [Field K] [Field E] [Algebra K E] [Monoid G]
  [AddCommGroup V] [Module K V]

/-- A subrepresentation of a scalar extension which contains a nonzero vector
from the original irreducible representation is the whole scalar extension. -/
theorem baseChange_subrepresentation_eq_top_of_tmul_mem
    (ρ : Representation K G V) [ρ.IsIrreducible]
    (S : Subrepresentation (ρ.baseChange E)) {v : V} (hv : v ≠ 0)
    (hSv : (1 : E) ⊗ₜ[K] v ∈ S) : S = ⊤ := by
  let T : Subrepresentation ρ :=
    ⟨(S.toSubmodule.restrictScalars K).comap (TensorProduct.mk K E V 1), by
      intro g w hw
      exact S.apply_mem_toSubmodule g hw⟩
  have hT : T = ⊤ := by
    rcases eq_bot_or_eq_top T with h | h
    · have : v ∈ T := hSv
      rw [h] at this
      exact (hv this).elim
    · exact h
  apply Subrepresentation.toSubmodule_injective
  apply top_unique
  intro x hx
  clear hx
  induction x using TensorProduct.inductionOn with
  | tmul a w =>
    have hw : w ∈ T := by rw [hT]; trivial
    have hw' : (1 : E) ⊗ₜ[K] w ∈ S := hw
    simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using
      S.toSubmodule.smul_mem a hw'
  | add x y hx hy => exact S.toSubmodule.add_mem hx hy

end Representation


namespace Representation

variable {K E G V : Type*} [Field K] [Field E] [Algebra K E] [Monoid G]
  [AddCommGroup V] [Module K V]

/-- An irreducible representation with a split rank-two involution stays
irreducible over every extension of its coefficient field. -/
theorem isIrreducible_baseChange_of_involution_basis
    (ρ : Representation K G V) [ρ.IsIrreducible] (hK : (2 : K) ≠ 0)
    (b : Module.Basis (Fin 2) K V) (c : G)
    (h0 : ρ c (b 0) = b 0) (h1 : ρ c (b 1) = -b 1) :
    (ρ.baseChange E).IsIrreducible := by
  let bE := b.baseChange E
  have hE : (2 : E) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K E)).mpr hK
  have h0E : ρ.baseChange E c (bE 0) = bE 0 := by
    simp only [bE, Module.Basis.baseChange_apply, baseChange_tmul, h0]
  have h1E : ρ.baseChange E c (bE 1) = -bE 1 := by
    simp only [bE, Module.Basis.baseChange_apply, baseChange_tmul, h1,
      TensorProduct.tmul_neg]
  let : Nontrivial (Subrepresentation (ρ.baseChange E)) := ⟨⟨⊥, ⊤, by
    intro h
    have hm : bE 0 ∈ (⊥ : Subrepresentation (ρ.baseChange E)) := by rw [h]; trivial
    exact bE.ne_zero 0 hm⟩⟩
  apply IsSimpleOrder.of_forall_eq_top
  intro S hS
  have hS' : S.toSubmodule ≠ ⊥ := by
    intro h
    exact hS (Subrepresentation.toSubmodule_injective h)
  obtain ⟨i, hi⟩ := bE.exists_mem_of_involution hE (ρ.baseChange E c) h0E h1E
    S.toSubmodule hS' (fun w hw => S.apply_mem_toSubmodule c hw)
  apply baseChange_subrepresentation_eq_top_of_tmul_mem ρ S (b.ne_zero i)
  change (1 : E) ⊗ₜ[K] b i ∈ S.toSubmodule
  simpa only [bE, Module.Basis.baseChange_apply] using hi

/-- An odd irreducible rank-two representation is absolutely irreducible:
it remains irreducible after every field extension. The characteristic
hypothesis is only that two is nonzero. -/
theorem isIrreducible_baseChange_of_involution
    (ρ : Representation K G (Fin 2 → K)) [ρ.IsIrreducible] (hK : (2 : K) ≠ 0)
    (c : G) (hc : c ^ 2 = 1) (hdet : LinearMap.det (ρ c) = -1) :
    (ρ.baseChange E).IsIrreducible := by
  let M := LinearMap.toMatrixAlgEquiv' (ρ c)
  have hM : M ^ 2 = 1 := by
    change LinearMap.toMatrixAlgEquiv' (ρ c) ^ 2 = 1
    rw [← map_pow, ← map_pow, hc, map_one, map_one]
  have hd : M.det = -1 := by
    change (LinearMap.toMatrix' (ρ c)).det = -1
    rw [LinearMap.det_toMatrix', hdet]
  obtain ⟨b, h0, h1⟩ := HilbertModularity.exists_basis_of_involution hK M hM hd
  apply isIrreducible_baseChange_of_involution_basis ρ hK b c
  · change (LinearMap.toMatrix' (ρ c)).mulVec (b 0) = b 0 at h0
    simpa only [LinearMap.toMatrix'_mulVec] using h0
  · change (LinearMap.toMatrix' (ρ c)).mulVec (b 1) = -b 1 at h1
    simpa only [LinearMap.toMatrix'_mulVec] using h1

end Representation
