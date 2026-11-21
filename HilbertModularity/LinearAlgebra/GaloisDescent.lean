/- Assembled by AxiomProver. -/

module

public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.Tactic.FieldSimp

/-! # Galois descent of lines

A line in a coordinate space over a Galois extension descends when it is
invariant under coefficient automorphisms. Normalizing one nonzero coordinate
makes every coordinate Galois-fixed, hence a member of the ground field.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Submodule

variable {K L ι : Type*} [Field K] [Field L] [Algebra K L]

/-- Membership of a ground-field vector in a subspace is reflected by scalar extension. -/
theorem one_tmul_mem_baseChange_iff {V : Type*} [AddCommGroup V] [Module K V]
    (P : Submodule K V) (v : V) : (1 : L) ⊗ₜ[K] v ∈ P.baseChange L ↔ v ∈ P := by
  rw [← span_singleton_le_iff_mem v P, ← baseChange_le_iff (A := L),
    baseChange_span, Set.image_singleton]
  exact (span_singleton_le_iff_mem _ _).symm

/-- Invariance of a line makes every ratio to a nonzero coordinate Galois-fixed. -/
theorem galois_fixed_coordinate_ratio (v : ι → L) (i : ι) (hi : v i ≠ 0)
    (hv : ∀ σ : L ≃ₐ[K] L, (fun j => σ (v j)) ∈ L ∙ v)
    (σ : L ≃ₐ[K] L) (j : ι) : σ (v j / v i) = v j / v i := by
  obtain ⟨c, hc⟩ := mem_span_singleton.mp (hv σ)
  have hci : c * v i = σ (v i) := congrFun hc i
  have hcj : c * v j = σ (v j) := congrFun hc j
  have hc0 : c ≠ 0 := by
    intro h
    have hz : σ (v i) = 0 := by simpa [h] using hci.symm
    exact hi (σ.injective (by simpa using hz))
  rw [map_div₀, ← hci, ← hcj, mul_div_mul_left _ _ hc0]

variable [IsGalois K L]

/-- A Galois-invariant line has a nonzero generator with coordinates in the ground field. -/
theorem exists_ground_field_generator (v : ι → L) (hv0 : v ≠ 0)
    (hv : ∀ σ : L ≃ₐ[K] L, (fun j => σ (v j)) ∈ L ∙ v) :
    ∃ u : ι → K, u ≠ 0 ∧ L ∙ v = L ∙ (fun j => algebraMap K L (u j)) := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := Function.ne_iff.mp hv0
  have hrat (j : ι) : v j / v i ∈ Set.range (algebraMap K L) :=
    (InfiniteGalois.mem_range_algebraMap_iff_fixed _).mpr
      (fun σ => galois_fixed_coordinate_ratio v i hi hv σ j)
  choose u hu using hrat
  have hui : u i = 1 := (algebraMap K L).injective (by simpa [hi] using hu i)
  refine ⟨u, ?_, ?_⟩
  · intro h
    have := congrFun h i
    simp [hui] at this
  · have he : v = v i • (fun j => algebraMap K L (u j)) := by
      ext j
      simp only [Pi.smul_apply, smul_eq_mul, hu]
      field_simp
    rw [he]
    exact span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hi) _

/-- Every coefficientwise Galois-invariant one-dimensional subspace is generated over the
extension field by a nonzero vector defined over the ground field. -/
theorem exists_ground_field_generator_of_finrank_one (S : Submodule L (ι → L))
    (hdim : Module.finrank L S = 1)
    (hS : ∀ (σ : L ≃ₐ[K] L) (v : ι → L), v ∈ S → (fun j => σ (v j)) ∈ S) :
    ∃ u : ι → K, u ≠ 0 ∧ S = L ∙ (fun j => algebraMap K L (u j)) := by
  obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.mp hdim
  have hv0' : (v : ι → L) ≠ 0 := fun h => hv0 (Subtype.ext h)
  have hspan : L ∙ (v : ι → L) = S := by
    apply le_antisymm
    · exact (span_singleton_le_iff_mem _ _).mpr v.property
    · intro w hw
      obtain ⟨c, hc⟩ := hv ⟨w, hw⟩
      exact mem_span_singleton.mpr ⟨c, congrArg Subtype.val hc⟩
  obtain ⟨u, hu, he⟩ := exists_ground_field_generator (K := K) (v : ι → L) hv0'
    (fun σ => by simpa only [hspan] using hS σ v v.property)
  exact ⟨u, hu, hspan.symm.trans he⟩

end Submodule

namespace TensorProduct

variable {K L V : Type*} [Field K] [Field L] [Algebra K L]
  [AddCommGroup V] [Module K V]

/-- A coefficient-field automorphism acts on the first factor of a scalar extension. -/
def coefficientGaloisEquiv (σ : L ≃ₐ[K] L) : (L ⊗[K] V) ≃ₗ[K] (L ⊗[K] V) :=
  TensorProduct.congr σ.toLinearEquiv (LinearEquiv.refl K V)

/-- The coefficient action on pure tensors leaves the original vector unchanged. -/
@[simp]
theorem coefficientGaloisEquiv_tmul (σ : L ≃ₐ[K] L) (a : L) (v : V) :
    coefficientGaloisEquiv σ (a ⊗ₜ[K] v) = σ a ⊗ₜ[K] v := rfl

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-- The coefficient Galois action is semilinear over the extension field. -/
def coefficientGaloisSemilinearEquiv (σ : L ≃ₐ[K] L) :
    LinearEquiv (σ.toRingEquiv : L →+* L)
      (σ' := (σ.toRingEquiv.symm : L →+* L)) (L ⊗[K] V) (L ⊗[K] V) :=
  { (coefficientGaloisEquiv σ).toAddEquiv with
    map_smul' := fun a x => by
      change coefficientGaloisEquiv σ (a • x) = σ a • coefficientGaloisEquiv σ x
      induction x using TensorProduct.inductionOn with
      | tmul b v => simp [smul_tmul', smul_eq_mul]
      | add x y hx hy => simp only [smul_add, map_add, hx, hy] }

/-- The semilinear coefficient action has the same underlying function as the ground-linear one. -/
@[simp]
theorem coefficientGaloisSemilinearEquiv_apply (σ : L ≃ₐ[K] L) (x : L ⊗[K] V) :
    coefficientGaloisSemilinearEquiv σ x = coefficientGaloisEquiv σ x := rfl

end TensorProduct

namespace Module.Basis

variable {K L V ι : Type*} [Field K] [Field L] [Algebra K L]
  [AddCommGroup V] [Module K V] [Finite ι]

/-- In an extended ground-field basis, coefficient Galois action acts on each coordinate. -/
theorem baseChange_equivFun_coefficientGaloisEquiv (b : Basis ι K V)
    (σ : L ≃ₐ[K] L) (x : L ⊗[K] V) (i : ι) :
    (b.baseChange L).equivFun (TensorProduct.coefficientGaloisEquiv σ x) i =
      σ ((b.baseChange L).equivFun x i) := by
  induction x using TensorProduct.inductionOn with
  | tmul a v => simp [Basis.equivFun_apply, Algebra.smul_def, σ.commutes]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

end Module.Basis

namespace Submodule

variable {K L V ι : Type*} [Field K] [Field L] [Algebra K L]
  [IsGalois K L]
  [AddCommGroup V] [Module K V] [Finite ι]

/-- An invariant line in an actual scalar-extension tensor has a nonzero ground-field generator. -/
theorem exists_tmul_generator_of_finrank_one (b : Module.Basis ι K V)
    (S : Submodule L (L ⊗[K] V)) (hdim : Module.finrank L S = 1)
    (hS : ∀ (σ : L ≃ₐ[K] L) (x : L ⊗[K] V), x ∈ S →
      TensorProduct.coefficientGaloisEquiv σ x ∈ S) :
    ∃ v : V, v ≠ 0 ∧ S = L ∙ ((1 : L) ⊗ₜ[K] v) := by
  let e := (b.baseChange L).equivFun
  let T := S.map e.toLinearMap
  have hdimT : Module.finrank L T = 1 := (e.finrank_map_eq S).trans hdim
  have hT (σ : L ≃ₐ[K] L) (w : ι → L) (hw : w ∈ T) : (fun i => σ (w i)) ∈ T := by
    obtain ⟨x, hx, rfl⟩ := mem_map.mp hw
    refine mem_map.mpr ⟨TensorProduct.coefficientGaloisEquiv σ x, hS σ x hx, ?_⟩
    ext i
    exact b.baseChange_equivFun_coefficientGaloisEquiv σ x i
  obtain ⟨u, hu, hTu⟩ := exists_ground_field_generator_of_finrank_one T hdimT hT
  let v := b.equivFun.symm u
  have hv : v ≠ 0 := by
    intro h
    apply hu
    have he := congrArg b.equivFun h
    simpa [v] using he
  have he : e ((1 : L) ⊗ₜ[K] v) = fun i => algebraMap K L (u i) := by
    ext i
    change (b.baseChange L).equivFun ((1 : L) ⊗ₜ[K] v) i = _
    rw [Module.Basis.equivFun_apply, Module.Basis.baseChange_repr_tmul]
    simp only [Algebra.smul_def, mul_one]
    change algebraMap K L (b.equivFun (b.equivFun.symm u) i) = _
    rw [b.equivFun.apply_symm_apply]
  refine ⟨v, hv, ?_⟩
  apply map_injective_of_injective e.injective
  change T = (L ∙ ((1 : L) ⊗ₜ[K] v)).map e.toLinearMap
  rw [map_span, Set.image_singleton]
  exact hTu.trans (congrArg (fun w : ι → L => L ∙ w) he).symm

end Submodule
