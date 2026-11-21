/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.HodgeTateComparison
public import HilbertModularity.RepresentationTheory.CoefficientDecomposition
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! # Period spaces of coefficient decompositions

The actual completed period tensor commutes with finite products of
representations. Consequently the coefficient-idempotent decomposition also
decomposes every cyclotomic period eigenspace.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Representation

/-- Restriction of scalars commutes with the coordinatewise product action. -/
theorem restrictScalars_pi (R : Type*) {S G I : Type*}
    [CommSemiring R] [CommSemiring S] [Algebra R S] [Monoid G]
    {V : I → Type*} [∀ i, AddCommMonoid (V i)] [∀ i, Module S (V i)]
    [∀ i, Module R (V i)] [∀ i, IsScalarTower R S (V i)]
    (ρ : (i : I) → Representation S G (V i)) :
    (pi ρ).restrictScalars R = pi (fun i => (ρ i).restrictScalars R) := by
  ext g v i
  rfl

end Representation

namespace HodgeTate

variable (p : ℕ) [Fact p.Prime]
variable {G I : Type*} [Group G] [Fintype I] [DecidableEq I]
  {V : I → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℚ_[p] (V i)]
variable (ι : G →* (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p))

/-- The period tensor of a finite product is the product of its period tensors. -/
def periodPiLinearEquiv :
    (ℂ_[p] ⊗[ℚ_[p]] ((i : I) → V i)) ≃ₗ[ℂ_[p]]
      ((i : I) → ℂ_[p] ⊗[ℚ_[p]] V i) :=
  TensorProduct.piRight ℚ_[p] ℂ_[p] ℂ_[p] V

/-- Distribution of the period tensor commutes with every diagonal Galois action. -/
theorem periodPiLinearEquiv_apply_action (ρ : (i : I) → Representation ℚ_[p] G (V i))
    (g : G) (x : ℂ_[p] ⊗[ℚ_[p]] ((i : I) → V i)) (i : I) :
    periodPiLinearEquiv p (periodRepresentation p ι (Representation.pi ρ) g x) i =
      periodRepresentation p ι (ρ i) g (periodPiLinearEquiv p x i) := by
  induction x using TensorProduct.inductionOn with
  | tmul c v => rfl
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

/-- A product period has a given weight precisely when every component does. -/
theorem periodPiLinearEquiv_mem_weightSpace
    (ρ : (i : I) → Representation ℚ_[p] G (V i)) (q : ℤ)
    (x : ℂ_[p] ⊗[ℚ_[p]] ((i : I) → V i)) :
    x ∈ weightSpace p ι (Representation.pi ρ) q ↔
      ∀ i, periodPiLinearEquiv p x i ∈ weightSpace p ι (ρ i) q := by
  simp only [mem_weightSpace]
  rw [forall_comm]
  apply forall_congr'
  intro g
  rw [← (periodPiLinearEquiv p (V := V)).injective.eq_iff]
  have hs (a : ℚ_[p]) : periodPiLinearEquiv p (a • x) = a • periodPiLinearEquiv p x :=
    (periodPiLinearEquiv p (V := V)).toLinearMap.map_smul_of_tower a x
  rw [hs]
  exact (funext_iff).trans (forall_congr' fun i => by
    rw [periodPiLinearEquiv_apply_action]
    rfl)

section LocalBaseField

variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [Algebra K ℂ_[p]]
  [IsScalarTower ℚ_[p] K ℂ_[p]]
  (hK : ∀ (g : G) (a : K), PadicComplex.galoisEquiv p (ι g)
    (algebraMap K ℂ_[p] a) = algebraMap K ℂ_[p] a)

/-- Each actual local-base-field weight space of a finite product decomposes componentwise. -/
def localWeightSpacePiEquiv (ρ : (i : I) → Representation ℚ_[p] G (V i)) (q : ℤ) :
    localWeightSpace p ι hK (Representation.pi ρ) q ≃ₗ[K]
      ((i : I) → localWeightSpace p ι hK (ρ i) q) where
  toFun x i := ⟨periodPiLinearEquiv p x i,
    (periodPiLinearEquiv_mem_weightSpace p ι ρ q x).mp x.property i⟩
  invFun y := ⟨(periodPiLinearEquiv p).symm (fun i => (y i : ℂ_[p] ⊗[ℚ_[p]] V i)), by
    apply (periodPiLinearEquiv_mem_weightSpace p ι ρ q _).mpr
    intro i
    rw [(periodPiLinearEquiv p).apply_symm_apply]
    exact (y i).property⟩
  left_inv x := by
    apply Subtype.ext
    exact (periodPiLinearEquiv p (V := V)).symm_apply_apply (x : ℂ_[p] ⊗[ℚ_[p]] ((i : I) → V i))
  right_inv y := by
    ext i
    exact congrArg (fun z => z i) ((periodPiLinearEquiv p).apply_symm_apply
      (fun i => (y i : ℂ_[p] ⊗[ℚ_[p]] V i)))
  map_add' x y := by
    ext i
    exact congrArg (fun z => z i) ((periodPiLinearEquiv p (V := V)).map_add (x : ℂ_[p] ⊗[ℚ_[p]] ((i : I) → V i)) (y : ℂ_[p] ⊗[ℚ_[p]] ((i : I) → V i)))
  map_smul' a x := by
    ext i
    exact congrArg (fun z => z i)
      ((periodPiLinearEquiv p (V := V)).toLinearMap.map_smul_of_tower a (x : ℂ_[p] ⊗[ℚ_[p]] ((i : I) → V i)))

end LocalBaseField

/-- A weight space of a finite product vanishes exactly when each component weight space does. -/
theorem weightSpace_pi_eq_bot_iff (ρ : (i : I) → Representation ℚ_[p] G (V i)) (q : ℤ) :
    weightSpace p ι (Representation.pi ρ) q = ⊥ ↔
      ∀ i, weightSpace p ι (ρ i) q = ⊥ := by
  let e := periodPiLinearEquiv p (V := V)
  constructor
  · intro h i
    apply eq_bot_iff.mpr
    intro x hx
    have hy : e.symm (Pi.single i x) ∈ weightSpace p ι (Representation.pi ρ) q := by
      apply (periodPiLinearEquiv_mem_weightSpace p ι ρ q _).mpr
      intro j
      change e (e.symm (Pi.single i x)) j ∈ weightSpace p ι (ρ j) q
      rw [e.apply_symm_apply]
      by_cases hj : j = i
      · subst j
        simpa using hx
      · simp [Pi.single_eq_of_ne hj]
    have hy0 : e.symm (Pi.single i x) = 0 := by simpa [h] using hy
    have he := congrArg (fun y => e y i) hy0
    simpa using he
  · intro h
    apply eq_bot_iff.mpr
    intro x hx
    apply e.injective
    ext i
    have hi := (periodPiLinearEquiv_mem_weightSpace p ι ρ q x).mp hx i
    simpa [h i] using hi

/-- Insert one completed period into a finite product of representations. -/
def periodPiSingle (i : I) : (ℂ_[p] ⊗[ℚ_[p]] V i) →ₗ[ℂ_[p]]
    ℂ_[p] ⊗[ℚ_[p]] ((j : I) → V j) :=
  (periodPiLinearEquiv p (V := V)).symm.toLinearMap.comp
    (LinearMap.single ℂ_[p] (fun j => ℂ_[p] ⊗[ℚ_[p]] V j) i)

/-- Inserting a component period preserves its cyclotomic weight. -/
theorem periodPiSingle_mem_weightSpace
    (ρ : (i : I) → Representation ℚ_[p] G (V i)) (q : ℤ) (i : I)
    (x : ℂ_[p] ⊗[ℚ_[p]] V i) (hx : x ∈ weightSpace p ι (ρ i) q) :
    periodPiSingle p i x ∈ weightSpace p ι (Representation.pi ρ) q := by
  apply (periodPiLinearEquiv_mem_weightSpace p ι ρ q _).mpr
  intro j
  change periodPiLinearEquiv p ((periodPiLinearEquiv p).symm (Pi.single i x)) j ∈ _
  rw [(periodPiLinearEquiv p).apply_symm_apply]
  by_cases hj : j = i
  · subst j
    simpa using hx
  · simp [Pi.single_eq_of_ne hj]

/-- Inserting a component sends its fixed-period span into the product fixed-period span. -/
theorem periodPiSingle_mem_zeroWeightSpan
    (ρ : (i : I) → Representation ℚ_[p] G (V i)) (i : I)
    (x : ℂ_[p] ⊗[ℚ_[p]] V i) (hx : x ∈ zeroWeightSpan (ι := ι) (ρ i)) :
    periodPiSingle p i x ∈ zeroWeightSpan (ι := ι) (Representation.pi ρ) := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span (periodPiSingle_mem_weightSpace p ι ρ 0 i x hx)
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih => simpa only [map_smul] using Submodule.smul_mem _ c ih

/-- A finite product is spanned by fixed periods precisely when every factor is. -/
theorem zeroWeightSpan_pi_eq_top_iff (ρ : (i : I) → Representation ℚ_[p] G (V i)) :
    zeroWeightSpan (ι := ι) (Representation.pi ρ) = ⊤ ↔
      ∀ i, zeroWeightSpan (ι := ι) (ρ i) = ⊤ := by
  constructor
  · intro h i
    let f : (Representation.pi ρ).IntertwiningMap (ρ i) :=
      ⟨LinearMap.proj i, by intro g; ext v; rfl⟩
    apply zeroWeightSpan_eq_top_of_surjective (ι := ι) f _ h
    intro v
    exact ⟨Pi.single i v, by simp [f]⟩
  · intro h
    apply top_unique
    intro x _
    let e := periodPiLinearEquiv p (V := V)
    have he : (∑ i, periodPiSingle p i (e x i)) = x := by
      apply e.injective
      rw [map_sum]
      change (∑ i, e (e.symm (Pi.single i (e x i)))) = e x
      simp only [e.apply_symm_apply]
      exact LinearMap.sum_single_apply _ (e x)
    rw [← he]
    apply Submodule.sum_mem
    intro i _
    apply periodPiSingle_mem_zeroWeightSpan p ι ρ
    rw [h i]
    trivial

section CoefficientFields

variable {E L U : Type*} [Field E] [Field L]
  [Algebra ℚ_[p] E] [Algebra ℚ_[p] L] [FiniteDimensional ℚ_[p] E]
  [Algebra.IsSeparable ℚ_[p] E] [AddCommGroup U] [Module L U]
  [Module ℚ_[p] U] [IsScalarTower ℚ_[p] L U]
  [Module (L ⊗[ℚ_[p]] E) U] [IsScalarTower L (L ⊗[ℚ_[p]] E) U]
  (hL : ∀ x : E, ((minpoly ℚ_[p] x).map (algebraMap ℚ_[p] L)).Splits)
  (ρ : Representation L G U)
  (hρ : ∀ (g : G) (a : L ⊗[ℚ_[p]] E) (v : U), ρ g (a • v) = a • ρ g v)

/-- A period weight vanishes on a coefficient representation exactly when it
vanishes on every actual coefficient-idempotent summand. -/
theorem weightSpace_coefficientDecomposition_eq_bot_iff (q : ℤ) :
    weightSpace p ι (ρ.restrictScalars ℚ_[p]) q = ⊥ ↔
      ∀ σ : E →ₐ[ℚ_[p]] L, weightSpace p ι
        ((Representation.coefficientSubrepresentation ℚ_[p] E L hL ρ hρ σ).toRepresentation.restrictScalars ℚ_[p]) q = ⊥ := by
  classical
  rw [weightSpace_eq_bot_iff
    ((Representation.coefficientDecompositionEquiv ℚ_[p] E L hL ρ hρ).restrictScalars ℚ_[p]) q, Representation.restrictScalars_pi]
  exact weightSpace_pi_eq_bot_iff p ι _ q

/-- Fixed periods span a coefficient representation exactly when they span each
of its actual coefficient-idempotent summands. -/
theorem zeroWeightSpan_coefficientDecomposition_eq_top_iff :
    zeroWeightSpan (ι := ι) (ρ.restrictScalars ℚ_[p]) = ⊤ ↔
      ∀ σ : E →ₐ[ℚ_[p]] L, zeroWeightSpan (ι := ι)
        ((Representation.coefficientSubrepresentation ℚ_[p] E L hL ρ hρ σ).toRepresentation.restrictScalars ℚ_[p]) = ⊤ := by
  classical
  rw [zeroWeightSpan_eq_top_iff
    ((Representation.coefficientDecompositionEquiv ℚ_[p] E L hL ρ hρ).restrictScalars ℚ_[p]),
    Representation.restrictScalars_pi]
  exact zeroWeightSpan_pi_eq_top_iff p ι _

variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [Algebra K ℂ_[p]]
  [IsScalarTower ℚ_[p] K ℂ_[p]]
  (hK : ∀ (g : G) (a : K), PadicComplex.galoisEquiv p (ι g)
    (algebraMap K ℂ_[p] a) = algebraMap K ℂ_[p] a)

/-- Local-base-field period spaces decompose according to the actual coefficient
idempotents. No Hodge–Tate comparison is assumed in this algebraic identification. -/
def localWeightSpaceCoefficientEquiv (q : ℤ) :
    localWeightSpace p ι hK (ρ.restrictScalars ℚ_[p]) q ≃ₗ[K]
      ((σ : E →ₐ[ℚ_[p]] L) → localWeightSpace p ι hK
        ((Representation.coefficientSubrepresentation ℚ_[p] E L hL ρ hρ σ).toRepresentation.restrictScalars ℚ_[p]) q) := by
  classical
  let τ := fun σ : E →ₐ[ℚ_[p]] L =>
    (Representation.coefficientSubrepresentation ℚ_[p] E L hL ρ hρ σ).toRepresentation
  have e : localWeightSpace p ι hK (ρ.restrictScalars ℚ_[p]) q ≃ₗ[K]
      localWeightSpace p ι hK (Representation.pi fun σ => (τ σ).restrictScalars ℚ_[p]) q := by
    rw [← Representation.restrictScalars_pi]
    exact localWeightSpaceEquiv p ι hK
      ((Representation.coefficientDecompositionEquiv ℚ_[p] E L hL ρ hρ).restrictScalars ℚ_[p]) q
  exact e.trans (localWeightSpacePiEquiv p ι hK _ q)

end CoefficientFields

end HodgeTate
