/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.TateModule
public import HilbertModularity.RepresentationTheory.ScalarExtension

/-! # Extending continuous integral Tate representations to rational coefficients -/

@[expose] public noncomputable section

open scoped TensorProduct

namespace TateModule

variable (p : ℕ) [Fact p.Prime] {G A : Type*} [Monoid G] [AddCommGroup A]
  (ρ : Representation ℤ_[p] G (integral p A))

variable [TopologicalSpace A] [TopologicalSpace G]
  (hρ : Continuous (fun gv : G × integral p A => ρ gv.1 gv.2))

include hρ

/-- Joint continuity of the integral action gives continuous rational orbit maps. -/
theorem continuous_baseChange_orbit (v : rational p A) :
    Continuous (fun g => ρ.baseChange ℚ_[p] g v) := by
  induction v using TensorProduct.inductionOn with
  | tmul c v =>
    have h : Continuous (fun g : G => toRational p A (ρ g v)) :=
      (continuous_toRational p A).comp
      (hρ.comp (continuous_id.prodMk continuous_const))
    apply (h.const_smul c).congr
    intro g
    change c • ((1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] ρ g v) = _
    rw [Representation.baseChange_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  | add v w hv hw =>
    simp only [map_add]
    exact hv.add hw

variable [LocallyCompactSpace G]

/-- The rational orbit map is linear with values in continuous functions. -/
def baseChangeOrbitLinearMap : rational p A →ₗ[ℚ_[p]] C(G, rational p A) where
  toFun v := ⟨fun g => ρ.baseChange ℚ_[p] g v,
    continuous_baseChange_orbit p ρ hρ v⟩
  map_add' v w := by
    ext g
    exact map_add (ρ.baseChange ℚ_[p] g) v w
  map_smul' c v := by
    ext g
    exact map_smul (ρ.baseChange ℚ_[p] g) c v

/-- Rational scalar extension preserves joint continuity for a locally compact acting group. -/
theorem continuous_baseChange :
    Continuous (fun gv : G × rational p A => ρ.baseChange ℚ_[p] gv.1 gv.2) := by
  have h : Continuous (baseChangeOrbitLinearMap p ρ hρ) := by
    apply (continuous_linearMap_iff p A _).mpr
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact (continuous_toRational p A).comp (hρ.comp continuous_swap)
  exact (h.comp continuous_snd).eval continuous_fst

end TateModule
