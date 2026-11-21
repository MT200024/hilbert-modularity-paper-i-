/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.Schur
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.Group.Quotient

/-! # Characters comparing representations with equal restrictions

We follow the Schur-lemma argument in
[TripathiGoswami, constant character comparison lemma].
-/

@[expose] public section

namespace Representation

section Algebraic

variable {K G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]

/-- The ratio of two representations agreeing on a normal subgroup is an
intertwining endomorphism of their common restriction. -/
def ratioIntertwiner (ρ σ : Representation K G V) (H : Subgroup G) [H.Normal]
    (hagree : ∀ h : H, σ h = ρ h) (g : G) :
    IntertwiningMap (ρ.comp H.subtype) (ρ.comp H.subtype) where
  toLinearMap := σ g * ρ g⁻¹
  isIntertwining' h := by
    change (σ g * ρ g⁻¹) * ρ h = ρ h * (σ g * ρ g⁻¹)
    let h' : H := ⟨g⁻¹ * h * g, Subgroup.Normal.conj_mem' (inferInstance : H.Normal) (h : G) h.property g⟩
    have hh : σ (g⁻¹ * h * g) = ρ (g⁻¹ * h * g) := hagree h'
    calc
      (σ g * ρ g⁻¹) * ρ h = σ g * ρ (g⁻¹ * h * g) * ρ g⁻¹ := by
        simp [mul_assoc, ← map_mul]
      _ = σ g * σ (g⁻¹ * h * g) * ρ g⁻¹ := by rw [hh]
      _ = σ h * (σ g * ρ g⁻¹) := by
        rw [← map_mul]
        simp only [mul_inv_cancel_left, map_mul, mul_assoc]
      _ = ρ h * (σ g * ρ g⁻¹) := by rw [hagree h]

/-- Representations with equal absolutely irreducible restrictions to a normal
subgroup differ by a character trivial on that subgroup. -/
theorem exists_character_of_eq_on_normal_subgroup [CharZero K]
    [FiniteDimensional K V] [Nontrivial V]
    (ρ σ : Representation K G V) (H : Subgroup G) [H.Normal]
    (hagree : ∀ h : H, σ h = ρ h)
    (E : Type*) [Field E] [Algebra K E] [IsAlgClosed E]
    [Representation.IsIrreducible (Representation.baseChange E (ρ.comp H.subtype))] :
    ∃ χ : G →* Kˣ, (∀ h : H, χ h = 1) ∧ ∀ g, σ g = (χ g : K) • ρ g := by
  classical
  have hs (g : G) : ∃ a : K, σ g * ρ g⁻¹ = a • (1 : Module.End K V) :=
    IntertwiningMap.exists_eq_smul_id_of_baseChange_irreducible E (ρ.comp H.subtype)
      (ratioIntertwiner ρ σ H hagree g)
  choose a ha using hs
  have hact (g : G) : σ g = a g • ρ g := by
    have h := congrArg (fun f : Module.End K V => f * ρ g) (ha g)
    simpa only [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one,
      smul_mul_assoc, one_mul] using h
  have hinj (g : G) : Function.Injective (fun a : K => a • ρ g) := by
    apply smul_left_injective K
    simpa only [asGroupHom_apply] using (ρ.asGroupHom g).ne_zero
  let χ : G →* K :=
    { toFun := a
      map_one' := by
        apply hinj 1
        simpa only [map_one, one_smul] using (hact 1).symm
      map_mul' := by
        intro g h
        apply hinj (g * h)
        change a (g * h) • ρ (g * h) = (a g * a h) • ρ (g * h)
        rw [← hact, map_mul, hact g, hact h, smul_mul_smul_comm, ← map_mul] }
  refine ⟨MonoidHom.toHomUnits χ, ?_, ?_⟩
  · intro h
    apply Units.ext
    change a h = 1
    apply hinj h
    change a h • ρ h = (1 : K) • ρ h
    rw [← hact, hagree h, one_smul]
  · intro g
    exact hact g

/-- The one-dimensional representation associated to a multiplicative character. -/
def ofCharacter (χ : G →* Kˣ) : Representation K G K :=
  (algebraMap K (Module.End K K)).toMonoidHom.comp ((Units.coeHom K).comp χ)

/-- The character acts by multiplication on its coefficient line. -/
@[simp] theorem ofCharacter_apply (χ : G →* Kˣ) (g : G) (a : K) :
    ofCharacter χ g a = (χ g : K) * a := rfl

/-- A linear isomorphism intertwining up to a character is an isomorphism
from the tensor product with that character's one-dimensional representation. -/
noncomputable def characterTensorEquiv
    {W : Type*} [AddCommGroup W] [Module K W]
    (ρ : Representation K G W) (σ : Representation K G V) (χ : G →* Kˣ)
    (e : W ≃ₗ[K] V)
    (he : ∀ g v, σ g (e v) = (χ g : K) • e (ρ g v)) :
    ((ofCharacter χ).tprod ρ).Equiv σ :=
  Representation.Equiv.mk ((_root_.TensorProduct.lid K W).trans e) fun g => by
    apply _root_.TensorProduct.ext
    ext a
    simp [he, mul_comm]

end Algebraic

section Topological

variable {K G V : Type*} [NontriviallyNormedField K] [CharZero K] [CompleteSpace K]
  [Group G] [TopologicalSpace G] [ContinuousInv G]
  [NormedAddCommGroup V] [NormedSpace K V] [FiniteDimensional K V] [Nontrivial V]

/-- A scalar character comparing two continuous finite-dimensional
representations is automatically continuous. -/
theorem continuous_character_of_eq_smul
    (ρ σ : Representation K G V) (χ : G →* Kˣ)
    (hρ : ∀ v, Continuous (fun g => ρ g v)) (hσ : ∀ v, Continuous (fun g => σ g v))
    (hχ : ∀ g, σ g = (χ g : K) • ρ g) : Continuous χ := by
  let ρc : G → V →L[K] V := fun g => (ρ g).toContinuousLinearMap
  let σc : G → V →L[K] V := fun g => (σ g).toContinuousLinearMap
  have hρc : Continuous ρc := continuous_clm_apply.mpr hρ
  have hσc : Continuous σc := continuous_clm_apply.mpr hσ
  let t : (V →L[K] V) →ₗ[K] K :=
    (LinearMap.trace K V).comp (ContinuousLinearMap.coeLM K)
  have ht : Continuous (fun g => LinearMap.trace K V (σ g * ρ g⁻¹)) := by
    exact t.continuous_of_finiteDimensional.comp (hσc.mul (hρc.comp continuous_inv))
  have hn : (Module.finrank K V : K) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt Module.finrank_pos)
  have he (g : G) : LinearMap.trace K V (σ g * ρ g⁻¹) / (Module.finrank K V : K) =
      (χ g : K) := by
    rw [hχ g, smul_mul_assoc, ← map_mul, mul_inv_cancel, map_one, map_smul,
      LinearMap.trace_one, smul_eq_mul, mul_div_cancel_right₀ _ hn]
  apply Continuous.of_coeHom_comp
  change Continuous (fun g => (χ g : K))
  simpa only [he] using ht.div_const (Module.finrank K V : K)

/-- The comparison character descends continuously to the quotient by the
normal subgroup on which the representations agree. -/
theorem exists_quotient_character_of_eq_on_normal_subgroup
    (ρ σ : Representation K G V) (H : Subgroup G) [H.Normal]
    (hagree : ∀ h : H, σ h = ρ h)
    (hρ : ∀ v, Continuous (fun g => ρ g v)) (hσ : ∀ v, Continuous (fun g => σ g v))
    (E : Type*) [Field E] [Algebra K E] [IsAlgClosed E]
    [Representation.IsIrreducible (Representation.baseChange E (ρ.comp H.subtype))] :
    ∃ ν : G ⧸ H →* Kˣ, Continuous ν ∧ ∀ g, σ g = (ν (QuotientGroup.mk g) : K) • ρ g := by
  obtain ⟨χ, hH, hχ⟩ := exists_character_of_eq_on_normal_subgroup ρ σ H hagree E
  let ν := QuotientGroup.lift H χ (fun h hh => hH ⟨h, hh⟩)
  refine ⟨ν, ?_, hχ⟩
  rw [(QuotientGroup.isQuotientMap_mk H).continuous_iff]
  exact continuous_character_of_eq_smul ρ σ χ hρ hσ hχ

omit [Nontrivial V] in
/-- Isomorphic absolutely irreducible restrictions give a continuous quotient
character and an actual isomorphism with its tensor twist. -/
theorem exists_quotient_character_of_equiv_restriction
    {W : Type*} [NormedAddCommGroup W] [NormedSpace K W]
    [FiniteDimensional K W] [Nontrivial W]
    (ρ : Representation K G W) (σ : Representation K G V)
    (H : Subgroup G) [H.Normal]
    (e : Representation.Equiv (ρ.comp H.subtype) (σ.comp H.subtype))
    (hρ : ∀ v, Continuous (fun g => ρ g v)) (hσ : ∀ v, Continuous (fun g => σ g v))
    (E : Type*) [Field E] [Algebra K E] [IsAlgClosed E]
    [Representation.IsIrreducible (Representation.baseChange E (ρ.comp H.subtype))] :
    ∃ ν : G ⧸ H →* Kˣ, Continuous ν ∧
      Nonempty (((ofCharacter (ν.comp (QuotientGroup.mk' H))).tprod ρ).Equiv σ) := by
  let τ : Representation K G W := e.toLinearEquiv.symm.conjRingEquiv.toMonoidHom.comp σ
  have hagree (h : H) : τ h = ρ h := by
    apply LinearMap.ext
    intro v
    change e.toLinearEquiv.symm (σ h (e v)) = ρ h v
    have he : e (ρ h v) = σ h (e v) := congrArg (fun f : W →ₗ[K] V => f v) (e.isIntertwining' h)
    rw [← he]
    exact e.toLinearEquiv.symm_apply_apply _
  have hτ (v : W) : Continuous (fun g => τ g v) :=
    e.toLinearEquiv.symm.toLinearMap.continuous_of_finiteDimensional.comp (hσ (e v))
  obtain ⟨ν, hν, hact⟩ :=
    exists_quotient_character_of_eq_on_normal_subgroup ρ τ H hagree hρ hτ E
  refine ⟨ν, hν, ⟨characterTensorEquiv ρ σ (ν.comp (QuotientGroup.mk' H)) e.toLinearEquiv ?_⟩⟩
  intro g v
  have h := congrArg (fun f : Module.End K W => e (f v)) (hact g)
  change e.toLinearEquiv (e.toLinearEquiv.symm (σ g (e v))) =
    e.toLinearEquiv ((ν (QuotientGroup.mk g) : K) • ρ g v) at h
  simpa only [LinearEquiv.apply_symm_apply, map_smul, MonoidHom.comp_apply,
    QuotientGroup.mk'_apply, Representation.Equiv.toLinearEquiv_apply,
    Representation.Equiv.coe_toIntertwiningMap] using h

omit [Nontrivial V] in
/-- Continuous representations with isomorphic absolutely irreducible kernel
restrictions differ by a continuous character of the given quotient group.
Compactness and the Hausdorff property include the profinite setting of
[TripathiGoswami, constant character comparison lemma]. -/
theorem exists_character_of_equiv_kernel_restriction
    {Γ W : Type*} [Group Γ] [TopologicalSpace Γ] [T2Space Γ] [CompactSpace G]
    [NormedAddCommGroup W] [NormedSpace K W] [FiniteDimensional K W] [Nontrivial W]
    (π : G →* Γ) (hπ : Function.Surjective π) (hπc : Continuous π)
    (ρ : Representation K G W) (σ : Representation K G V)
    (e : Representation.Equiv (ρ.comp π.ker.subtype) (σ.comp π.ker.subtype))
    (hρ : ∀ v, Continuous (fun g => ρ g v)) (hσ : ∀ v, Continuous (fun g => σ g v))
    (E : Type*) [Field E] [Algebra K E] [IsAlgClosed E]
    [Representation.IsIrreducible (Representation.baseChange E (ρ.comp π.ker.subtype))] :
    ∃ ν : Γ →* Kˣ, Continuous ν ∧
      Nonempty (((ofCharacter (ν.comp π)).tprod ρ).Equiv σ) := by
  obtain ⟨χ, hχ, he⟩ :=
    exists_quotient_character_of_equiv_restriction ρ σ π.ker e hρ hσ E
  let q := QuotientGroup.quotientKerEquivOfSurjective π hπ
  let ν : Γ →* Kˣ := χ.comp q.symm.toMonoidHom
  have hq (g : G) : q (QuotientGroup.mk g) = π g := rfl
  have hcomp : ν.comp π = χ.comp (QuotientGroup.mk' π.ker) := by
    apply MonoidHom.ext
    intro g
    change χ (q.symm (π g)) = χ (QuotientGroup.mk g)
    rw [← hq g, q.symm_apply_apply]
  refine ⟨ν, ?_, ?_⟩
  · rw [(Topology.IsQuotientMap.of_surjective_continuous hπ hπc).continuous_iff]
    have hc : Continuous (χ.comp (QuotientGroup.mk' π.ker)) :=
      hχ.comp QuotientGroup.continuous_mk
    rw [← hcomp] at hc
    exact hc
  · rw [hcomp]
    exact he

end Topological

end Representation
