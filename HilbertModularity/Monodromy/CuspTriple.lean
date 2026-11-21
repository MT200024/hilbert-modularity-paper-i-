/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Monodromy.Admissible
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import HilbertModularity.Monodromy.AbsoluteIrreducibility
public import HilbertModularity.Monodromy.CuspInvolution
public import HilbertModularity.RepresentationTheory.Quotient
public import HilbertModularity.RepresentationTheory.SurjectiveRestriction

/-! # The fixed lines of an oriented cusp triple

The product relation and the infinity class exclude a common fixed vector
for the two finite cusp monodromies. The three conjugating bases may differ.
-/

public noncomputable section

open Matrix

namespace HilbertModularity.Monodromy

variable {K G V : Type*} [Field K] [Group G]
  [AddCommGroup V] [Module K V]

/-- The infinity matrix has no fixed vector when its trace differs from two. -/
theorem Uinf_fixed_eq_zero (τ : K) (hτ : τ ≠ 2) (v : Fin 2 → K)
    (h : Uinf τ *ᵥ v = v) : v = 0 := by
  have hp : (U0 * U1 τ) *ᵥ v = v := by
    calc
      (U0 * U1 τ) *ᵥ v = (U0 * U1 τ) *ᵥ (Uinf τ *ᵥ v) :=
        congrArg (fun w => (U0 * U1 τ) *ᵥ w) h.symm
      _ = v := by rw [mulVec_mulVec, U0_mul_U1_mul_Uinf, one_mulVec]
  have h0 := congrFun hp 0
  have h1 := congrFun hp 1
  simp [U0, U1, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two] at h0 h1
  have hv0 : v 0 = 0 := h1.resolve_left (sub_ne_zero.mpr hτ)
  have hv1 : v 1 = 0 := by
    rw [hv0] at h0
    simpa using h0
  funext i
  fin_cases i <;> assumption

/-- Three prescribed local classes with product one have transverse finite
cusp fixed lines; no simultaneous choice of the three bases is assumed. -/
theorem fixed_eq_zero_of_cusp_triple
    (ρ : Representation K G V) (a b d : G) (hprod : a * b * d = 1)
    (τ : K) (hτ : τ ≠ 2) (c : Module.Basis (Fin 2) K V)
    (hc : LinearMap.toMatrix c c (ρ d) = Uinf τ)
    (v : V) (ha : ρ a v = v) (hb : ρ b v = v) : v = 0 := by
  have hab : ρ (a * b) v = v := by
    rw [map_mul, Module.End.mul_apply, hb, ha]
  have hdp : d * (a * b) = 1 := mul_eq_one_comm.mp hprod
  have hd : ρ d v = v := by
    calc
      ρ d v = ρ d (ρ (a * b) v) := congrArg (ρ d) hab.symm
      _ = v := by rw [← Module.End.mul_apply, ← map_mul, hdp, map_one]; rfl
  have hm : Uinf τ *ᵥ (c.equivFun v) = c.equivFun v := by
    rw [← hc]
    change (LinearMap.toMatrix c c (ρ d)) *ᵥ (c.repr v : Fin 2 → K) = c.repr v
    simpa only [hd] using LinearMap.toMatrix_mulVec_repr c c (ρ d) v
  have hz := Uinf_fixed_eq_zero τ hτ (c.equivFun v) hm
  exact c.equivFun.injective (hz.trans (map_zero c.equivFun).symm)

/-- The three standard conjugacy classes and their product relation suffice
for cusp-swap invariance. Coordinates carry the continuity hypothesis, so the
original fibre need not have a separately chosen norm. -/
theorem nonempty_equiv_comp_of_standard_cusp_triple
    {K G V : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [Group G] [TopologicalSpace G]
    [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) (a b d : G) (hprod : a * b * d = 1)
    (hdense : Dense (Subgroup.closure ({a, b} : Set G) : Set G))
    (α : G ≃* G) (hα : Continuous α) (ha : α a = b) (hb : α b = a)
    (τ : K) (hτ : τ ≠ 2)
    (c₀ c₁ c₂ : Module.Basis (Fin 2) K V)
    (hc₀ : LinearMap.toMatrix c₀ c₀ (ρ a) = U0)
    (hc₁ : LinearMap.toMatrix c₁ c₁ (ρ b) = U1 τ)
    (hc₂ : LinearMap.toMatrix c₂ c₂ (ρ d) = Uinf τ)
    (hρ : ∀ v, Continuous (fun g => c₀.equivFun (ρ g v))) :
    Nonempty (ρ.Equiv (ρ.comp α.toMonoidHom)) ∧
      (ρ.baseChange (AlgebraicClosure K)).IsIrreducible := by
  let e := c₀.equivFun
  let σ : Representation K G (Fin 2 → K) :=
    e.conjRingEquiv.toMonoidHom.comp ρ
  let E : ρ.Equiv σ := .mk e (by
    intro g
    apply LinearMap.ext
    intro v
    change e (ρ g v) = e (ρ g (e.symm (e v)))
    rw [LinearEquiv.symm_apply_apply])
  have hA : (ρ a - 1) ^ 2 = 0 := by
    apply (LinearMap.toMatrixAlgEquiv c₀).injective
    rw [map_pow, map_sub, map_one, map_zero]
    change (LinearMap.toMatrix c₀ c₀ (ρ a) - 1) ^ 2 = 0
    rw [hc₀]
    exact (U0_unipotent (R := K)).2
  have hB : (ρ b - 1) ^ 2 = 0 := by
    apply (LinearMap.toMatrixAlgEquiv c₁).injective
    rw [map_pow, map_sub, map_one, map_zero]
    change (LinearMap.toMatrix c₁ c₁ (ρ b) - 1) ^ 2 = 0
    rw [hc₁]
    exact (U1_unipotent τ hτ).2
  have hAne : ρ a ≠ 1 := by
    intro h
    exact (U0_unipotent (R := K)).1 (hc₀.symm.trans (by rw [h]; simp))
  have hBne : ρ b ≠ 1 := by
    intro h
    exact (U1_unipotent τ hτ).1 (hc₁.symm.trans (by rw [h]; simp))
  have hAc : (σ a - 1) ^ 2 = 0 := by
    change (e.conjRingEquiv (ρ a) - 1) ^ 2 = 0
    simpa only [map_pow, map_sub, map_one, map_zero] using congrArg e.conjRingEquiv hA
  have hBc : (σ b - 1) ^ 2 = 0 := by
    change (e.conjRingEquiv (ρ b) - 1) ^ 2 = 0
    simpa only [map_pow, map_sub, map_one, map_zero] using congrArg e.conjRingEquiv hB
  have hAnec : σ a ≠ 1 := by
    intro h
    apply hAne
    apply e.conjRingEquiv.injective
    exact h.trans (map_one e.conjRingEquiv).symm
  have hBnec : σ b ≠ 1 := by
    intro h
    apply hBne
    apply e.conjRingEquiv.injective
    exact h.trans (map_one e.conjRingEquiv).symm
  have hirr : ∀ v, σ a v = v → σ b v = v → v = 0 := by
    intro v hva hvb
    have hfixed (g : G) (hgv : σ g v = v) : ρ g (e.symm v) = e.symm v := by
      apply e.injective
      exact hgv.trans (e.apply_symm_apply v).symm
    have hz := fixed_eq_zero_of_cusp_triple ρ a b d hprod τ hτ c₂ hc₂
      (e.symm v) (hfixed a hva) (hfixed b hvb)
    exact e.symm.injective (hz.trans (map_zero e.symm).symm)
  obtain ⟨H⟩ := nonempty_equiv_comp_cusp_swap σ
    (fun v => hρ (e.symm v)) a b hdense α hα ha hb hAc hBc hAnec hBnec hirr
  refine ⟨⟨E.trans (H.trans (E.symm.compHom α.toMonoidHom))⟩, ?_⟩
  apply (OrderIso.isSimpleOrder_iff
    (E.baseChange (AlgebraicClosure K)).subrepresentationOrderIso).mpr
  exact isIrreducible_baseChange_of_unipotent_cusps (AlgebraicClosure K)
    σ a b hAc hBc hBnec hirr

end HilbertModularity.Monodromy
