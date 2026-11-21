/- Assembled by AxiomProver. -/

module

public import HilbertModularity.LinearAlgebra.GaloisDescent
public import HilbertModularity.RepresentationTheory.ScalarExtension
public import HilbertModularity.RepresentationTheory.HodgeTateFunctoriality
public import Mathlib.RepresentationTheory.Subrepresentation

/-! # Descent of stable lines

An invariant line of a scalar-extended representation descends when it is also
stable under the actual coefficient Galois action. This is the algebraic descent
step in [TripathiGoswami, descent of the weight-zero quotient].
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Representation

variable {K L G V ι : Type*} [Field K] [Field L] [Algebra K L]
  [IsGalois K L] [Monoid G]
  [AddCommGroup V] [Module K V] [Finite ι]

/-- A coefficientwise Galois-invariant stable line descends to a stable ground-field line,
with its actual scalar extension equal to the original subspace. -/
theorem exists_subrepresentation_baseChange_eq_of_galois_invariant
    (ρ : Representation K G V) (b : Module.Basis ι K V)
    (S : Subrepresentation (ρ.baseChange L)) (hdim : Module.finrank L S.toSubmodule = 1)
    (hS : ∀ (σ : L ≃ₐ[K] L) (x : L ⊗[K] V), x ∈ S →
      TensorProduct.coefficientGaloisEquiv σ x ∈ S) :
    ∃ T : Subrepresentation ρ, Module.finrank K T.toSubmodule = 1 ∧
      T.toSubmodule.baseChange L = S.toSubmodule := by
  obtain ⟨v, hv, hspan⟩ :=
    Submodule.exists_tmul_generator_of_finrank_one b S.toSubmodule hdim hS
  have he : (K ∙ v).baseChange L = S.toSubmodule := by
    rw [Submodule.baseChange_span, Set.image_singleton, hspan]
    rfl
  let T : Subrepresentation ρ :=
    { toSubmodule := K ∙ v
      apply_mem_toSubmodule := fun g w hw => by
        apply (Submodule.one_tmul_mem_baseChange_iff (L := L) (K ∙ v) (ρ g w)).mp
        rw [he]
        change (ρ.baseChange L) g ((1 : L) ⊗ₜ[K] w) ∈ S.toSubmodule
        apply S.apply_mem_toSubmodule g
        rw [← he]
        exact Submodule.tmul_mem_baseChange_of_mem 1 hw }
  exact ⟨T, finrank_span_singleton hv, he⟩

/-- In rank two, a stable rank-one quotient with Galois-invariant kernel descends, and the
descended quotient recovers the original quotient after scalar extension. -/
theorem exists_rank_one_quotient_of_galois_invariant_kernel
    (ρ : Representation K G V) (b : Module.Basis ι K V) (hV : Module.finrank K V = 2)
    (S : Subrepresentation (ρ.baseChange L))
    (hquot : Module.finrank L ((L ⊗[K] V) ⧸ S.toSubmodule) = 1)
    (hS : ∀ (σ : L ≃ₐ[K] L) (x : L ⊗[K] V), x ∈ S →
      TensorProduct.coefficientGaloisEquiv σ x ∈ S) :
    ∃ T : Subrepresentation ρ, Module.finrank K (V ⧸ T.toSubmodule) = 1 ∧
      T.baseChange L = S ∧
      Nonempty (((ρ.quotient T.toSubmodule T.apply_mem_toSubmodule).baseChange L).Equiv
        ((ρ.baseChange L).quotient S.toSubmodule S.apply_mem_toSubmodule)) := by
  let : FiniteDimensional K V := FiniteDimensional.of_finrank_eq_succ hV
  have hdim : Module.finrank L S.toSubmodule = 1 := by
    have h := S.toSubmodule.finrank_quotient_add_finrank
    rw [hquot, Module.finrank_baseChange, hV] at h
    omega
  obtain ⟨T, hT, he⟩ :=
    exists_subrepresentation_baseChange_eq_of_galois_invariant ρ b S hdim hS
  have hquotT : Module.finrank K (V ⧸ T.toSubmodule) = 1 := by
    have h := T.toSubmodule.finrank_quotient_add_finrank
    rw [hT, hV] at h
    omega
  have he' : T.baseChange L = S := Subrepresentation.toSubmodule_injective he
  refine ⟨T, hquotT, he', ?_⟩
  rw [← he']
  exact ⟨quotientBaseChangeEquiv L T⟩

omit [IsGalois K L]

/-- Coefficient Galois action commutes with the scalar-extended representation. -/
theorem coefficientGalois_apply_action (ρ : Representation K G V) (σ : L ≃ₐ[K] L)
    (g : G) (x : L ⊗[K] V) :
    TensorProduct.coefficientGaloisSemilinearEquiv σ ((ρ.baseChange L) g x) =
      (ρ.baseChange L) g (TensorProduct.coefficientGaloisSemilinearEquiv σ x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a v => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Coefficient automorphisms permute the actual stable subspaces after scalar extension. -/
def coefficientGaloisSubrepresentationEquiv (ρ : Representation K G V) (σ : L ≃ₐ[K] L) :
    Subrepresentation (ρ.baseChange L) ≃o Subrepresentation (ρ.baseChange L) :=
  Subrepresentation.semilinearOrderIso σ.toRingEquiv
    (TensorProduct.coefficientGaloisSemilinearEquiv σ) (coefficientGalois_apply_action ρ σ)

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-- Corresponding quotients under coefficient Galois action are semilinearly isomorphic. -/
def coefficientGaloisQuotientEquiv (ρ : Representation K G V) (σ : L ≃ₐ[K] L)
    (S : Subrepresentation (ρ.baseChange L)) :
    LinearEquiv (σ.toRingEquiv : L →+* L)
      (σ' := (σ.toRingEquiv.symm : L →+* L))
      ((L ⊗[K] V) ⧸ S.toSubmodule)
      ((L ⊗[K] V) ⧸ (coefficientGaloisSubrepresentationEquiv ρ σ S).toSubmodule) :=
  Submodule.Quotient.equiv _ _ (TensorProduct.coefficientGaloisSemilinearEquiv σ) rfl

/-- Coefficient Galois transport preserves the dimension of the quotient. -/
theorem finrank_coefficientGalois_quotient (ρ : Representation K G V) (σ : L ≃ₐ[K] L)
    (S : Subrepresentation (ρ.baseChange L)) :
    Module.finrank L ((L ⊗[K] V) ⧸
      (coefficientGaloisSubrepresentationEquiv ρ σ S).toSubmodule) =
        Module.finrank L ((L ⊗[K] V) ⧸ S.toSubmodule) := by
  let e := coefficientGaloisQuotientEquiv ρ σ S
  have h := lift_rank_eq_of_equiv_equiv σ.toRingEquiv e.toAddEquiv σ.bijective
    (fun r v => e.map_smulₛₗ r v)
  simpa only [Cardinal.toNat_lift, Module.finrank] using (congrArg Cardinal.toNat h).symm

/-- The induced quotient equivalence commutes with the quotient actions. -/
theorem coefficientGaloisQuotientEquiv_apply_action (ρ : Representation K G V)
    (σ : L ≃ₐ[K] L) (S : Subrepresentation (ρ.baseChange L))
    (g : G) (x : (L ⊗[K] V) ⧸ S.toSubmodule) :
    coefficientGaloisQuotientEquiv ρ σ S
      ((ρ.baseChange L).quotient S.toSubmodule S.apply_mem_toSubmodule g x) =
    (ρ.baseChange L).quotient
      (coefficientGaloisSubrepresentationEquiv ρ σ S).toSubmodule
      (coefficientGaloisSubrepresentationEquiv ρ σ S).apply_mem_toSubmodule g
        (coefficientGaloisQuotientEquiv ρ σ S x) := by
  refine Submodule.Quotient.induction_on _ x ?_
  intro v
  change Submodule.Quotient.mk
    (TensorProduct.coefficientGaloisSemilinearEquiv σ ((ρ.baseChange L) g v)) =
      Submodule.Quotient.mk ((ρ.baseChange L) g
        (TensorProduct.coefficientGaloisSemilinearEquiv σ v))
  rw [coefficientGalois_apply_action]

set_option maxHeartbeats 800000 in
/-- Coefficient Galois transport of quotients is an intertwining equivalence over a fixed subfield. -/
def coefficientGaloisQuotientRestrictScalarsEquiv
    (R : Type*) [Field R] [Algebra R K] [Algebra R L] [IsScalarTower R K L]
    (ρ : Representation K G V) (σ : L ≃ₐ[K] L) (S : Subrepresentation (ρ.baseChange L)) :
    (Representation.restrictScalars R
      ((ρ.baseChange L).quotient S.toSubmodule S.apply_mem_toSubmodule)).Equiv
    (Representation.restrictScalars R ((ρ.baseChange L).quotient
      (coefficientGaloisSubrepresentationEquiv ρ σ S).toSubmodule
      (coefficientGaloisSubrepresentationEquiv ρ σ S).apply_mem_toSubmodule)) :=
  .mk (LinearEquiv.restrictScalarsOfAlgEquiv R (σ.restrictScalars R)
    (coefficientGaloisQuotientEquiv ρ σ S)) (by
      intro g
      apply LinearMap.ext
      intro x
      exact coefficientGaloisQuotientEquiv_apply_action ρ σ S g x)

end Representation

namespace HodgeTate

variable {p : ℕ} [Fact p.Prime]
  {K L G V : Type*} [Field K] [Field L] [Algebra K L]
  [Algebra ℚ_[p] K] [Algebra ℚ_[p] L] [IsScalarTower ℚ_[p] K L]
  [Group G] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (ι : G →* (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- The unique quotient spanned by fixed periods has a coefficient-Galois invariant kernel. -/
theorem coefficientGalois_invariant_of_quotient_spanned_by_fixed_periods
    (ρ : Representation K G V) (hV : Module.finrank K V = 2)
    (hρ : zeroWeightSpan (ι := ι) ((ρ.baseChange L).restrictScalars ℚ_[p]) ≠ ⊤)
    (S : Subrepresentation (ρ.baseChange L))
    (hS : Module.finrank L ((L ⊗[K] V) ⧸ S.toSubmodule) = 1)
    (hfixed : zeroWeightSpan (ι := ι) (((ρ.baseChange L).quotient S.toSubmodule
      S.apply_mem_toSubmodule).restrictScalars ℚ_[p]) = ⊤) :
    ∀ (σ : L ≃ₐ[K] L) (x : L ⊗[K] V), x ∈ S →
      TensorProduct.coefficientGaloisEquiv σ x ∈ S := by
  intro σ x hx
  let T := Representation.coefficientGaloisSubrepresentationEquiv ρ σ S
  have hdimT : Module.finrank L ((L ⊗[K] V) ⧸ T.toSubmodule) = 1 :=
    (Representation.finrank_coefficientGalois_quotient ρ σ S).trans hS
  have hfixedT : zeroWeightSpan (ι := ι) (((ρ.baseChange L).quotient T.toSubmodule
      T.apply_mem_toSubmodule).restrictScalars ℚ_[p]) = ⊤ :=
    (zeroWeightSpan_eq_top_iff (ι := ι)
      (Representation.coefficientGaloisQuotientRestrictScalarsEquiv ℚ_[p] ρ σ S)).mp hfixed
  have he : T = S := eq_of_quotients_spanned_by_fixed_periods (ρ.baseChange L)
    (by rw [Module.finrank_baseChange, hV]) hρ T S hdimT hS hfixedT hfixed
  change TensorProduct.coefficientGaloisEquiv σ x ∈ S.toSubmodule
  rw [← he]
  exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- A rank-one quotient spanned by fixed periods descends over a Galois coefficient
extension when fixed periods do not span the whole rank-two representation. -/
theorem exists_descended_quotient_of_fixed_periods
    [IsGalois K L] {J : Type*} [Finite J]
    (ρ : Representation K G V) (b : Module.Basis J K V) (hV : Module.finrank K V = 2)
    (hρ : zeroWeightSpan (ι := ι) ((ρ.baseChange L).restrictScalars ℚ_[p]) ≠ ⊤)
    (S : Subrepresentation (ρ.baseChange L))
    (hS : Module.finrank L ((L ⊗[K] V) ⧸ S.toSubmodule) = 1)
    (hfixed : zeroWeightSpan (ι := ι) (((ρ.baseChange L).quotient S.toSubmodule
      S.apply_mem_toSubmodule).restrictScalars ℚ_[p]) = ⊤) :
    ∃ T : Subrepresentation ρ, Module.finrank K (V ⧸ T.toSubmodule) = 1 ∧
      T.baseChange L = S ∧
      zeroWeightSpan (ι := ι) (((ρ.quotient T.toSubmodule
        T.apply_mem_toSubmodule).baseChange L).restrictScalars ℚ_[p]) = ⊤ := by
  obtain ⟨T, hT, he, ⟨e⟩⟩ :=
    Representation.exists_rank_one_quotient_of_galois_invariant_kernel ρ b hV S hS
      (coefficientGalois_invariant_of_quotient_spanned_by_fixed_periods ι ρ hV hρ S hS hfixed)
  refine ⟨T, hT, he, ?_⟩
  exact (zeroWeightSpan_eq_top_iff (ι := ι) (e.restrictScalars ℚ_[p])).mpr hfixed

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- The descended quotient itself is spanned by fixed periods, before extending coefficients. -/
theorem exists_descended_quotient_spanned_by_fixed_periods
    [IsGalois K L] {J : Type*} [Finite J]
    [Module ℚ_[p] V] [IsScalarTower ℚ_[p] K V]
    (ρ : Representation K G V) (b : Module.Basis J K V) (hV : Module.finrank K V = 2)
    (hρ : zeroWeightSpan (ι := ι) ((ρ.baseChange L).restrictScalars ℚ_[p]) ≠ ⊤)
    (S : Subrepresentation (ρ.baseChange L))
    (hS : Module.finrank L ((L ⊗[K] V) ⧸ S.toSubmodule) = 1)
    (hfixed : zeroWeightSpan (ι := ι) (((ρ.baseChange L).quotient S.toSubmodule
      S.apply_mem_toSubmodule).restrictScalars ℚ_[p]) = ⊤) :
    ∃ T : Subrepresentation ρ, Module.finrank K (V ⧸ T.toSubmodule) = 1 ∧
      T.baseChange L = S ∧
      zeroWeightSpan (ι := ι) ((ρ.quotient T.toSubmodule
        T.apply_mem_toSubmodule).restrictScalars ℚ_[p]) = ⊤ := by
  obtain ⟨T, hT, he, hspan⟩ := exists_descended_quotient_of_fixed_periods ι ρ b hV hρ S hS hfixed
  exact ⟨T, hT, he, zeroWeightSpan_eq_top_of_baseChange _ hspan⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- Existence of a fixed-period rank-one quotient descends along a Galois coefficient extension
when the original rank-two representation is not itself spanned by fixed periods. -/
theorem exists_quotient_spanned_by_fixed_periods_of_galois_baseChange
    [IsGalois K L] [Module ℚ_[p] V] [IsScalarTower ℚ_[p] K V]
    (ρ : Representation K G V) (hV : Module.finrank K V = 2)
    (hρ : zeroWeightSpan (ι := ι) (ρ.restrictScalars ℚ_[p]) ≠ ⊤)
    (hex : ∃ S : Subrepresentation (ρ.baseChange L),
      Module.finrank L ((L ⊗[K] V) ⧸ S.toSubmodule) = 1 ∧
      zeroWeightSpan (ι := ι) (((ρ.baseChange L).quotient S.toSubmodule
        S.apply_mem_toSubmodule).restrictScalars ℚ_[p]) = ⊤) :
    ∃ T : Subrepresentation ρ, Module.finrank K (V ⧸ T.toSubmodule) = 1 ∧
      zeroWeightSpan (ι := ι) ((ρ.quotient T.toSubmodule
        T.apply_mem_toSubmodule).restrictScalars ℚ_[p]) = ⊤ := by
  obtain ⟨S, hS, hfixed⟩ := hex
  have hρL : zeroWeightSpan (ι := ι) ((ρ.baseChange L).restrictScalars ℚ_[p]) ≠ ⊤ :=
    fun h => hρ (zeroWeightSpan_eq_top_of_baseChange ρ h)
  obtain ⟨T, hT, _, hspan⟩ := exists_descended_quotient_spanned_by_fixed_periods ι ρ
    (Module.finBasis K V) hV hρL S hS hfixed
  exact ⟨T, hT, hspan⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- A fixed-period rank-one quotient descends along any algebraic coefficient extension,
provided fixed periods do not span the original rank-two representation. -/
theorem exists_quotient_spanned_by_fixed_periods_of_algebraic_baseChange
    [Algebra.IsAlgebraic K L] [Module ℚ_[p] V] [IsScalarTower ℚ_[p] K V]
    (ρ : Representation K G V) (hV : Module.finrank K V = 2)
    (hρ : zeroWeightSpan (ι := ι) (ρ.restrictScalars ℚ_[p]) ≠ ⊤)
    (hex : ∃ S : Subrepresentation (ρ.baseChange L),
      Module.finrank L ((L ⊗[K] V) ⧸ S.toSubmodule) = 1 ∧
      zeroWeightSpan (ι := ι) (((ρ.baseChange L).quotient S.toSubmodule
        S.apply_mem_toSubmodule).restrictScalars ℚ_[p]) = ⊤) :
    ∃ T : Subrepresentation ρ, Module.finrank K (V ⧸ T.toSubmodule) = 1 ∧
      zeroWeightSpan (ι := ι) ((ρ.quotient T.toSubmodule
        T.apply_mem_toSubmodule).restrictScalars ℚ_[p]) = ⊤ := by
  let : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective
  let : IsGalois K (AlgebraicClosure L) := inferInstance
  have hexTower := exists_quotient_spanned_by_fixed_periods_baseChange
    (ι := ι) (L := AlgebraicClosure L) (ρ.baseChange L) hex
  have hexClosure := (exists_quotient_spanned_by_fixed_periods_iff (ι := ι)
    (ρ.baseChangeTowerEquiv (L := L) (M := AlgebraicClosure L))).mp hexTower
  exact exists_quotient_spanned_by_fixed_periods_of_galois_baseChange ι ρ hV hρ hexClosure

/-- The concrete Hodge–Tate comparison and a nonzero period of nonzero weight
supply the non-spanning hypothesis for coefficient descent. -/
theorem exists_fixed_period_quotient_of_comparison
    [Algebra.IsAlgebraic K L] [Module ℚ_[p] V] [IsScalarTower ℚ_[p] K V]
    {F : Type*} [Field F] [Algebra ℚ_[p] F] [Algebra F ℂ_[p]]
    [IsScalarTower ℚ_[p] F ℂ_[p]]
    (hF : ∀ (g : G) (a : F), PadicComplex.galoisEquiv p (ι g)
      (algebraMap F ℂ_[p] a) = algebraMap F ℂ_[p] a)
    (ρ : Representation K G V) (hV : Module.finrank K V = 2)
    (hinj : Function.Injective (comparison p ι hF (ρ.restrictScalars ℚ_[p])))
    {q : ℤ} (hq : q ≠ 0) {x : ℂ_[p] ⊗[ℚ_[p]] V}
    (hx : x ∈ weightSpace p ι (ρ.restrictScalars ℚ_[p]) q) (hx0 : x ≠ 0)
    (hex : ∃ S : Subrepresentation (ρ.baseChange L),
      Module.finrank L ((L ⊗[K] V) ⧸ S.toSubmodule) = 1 ∧
      zeroWeightSpan (ι := ι) (((ρ.baseChange L).quotient S.toSubmodule
        S.apply_mem_toSubmodule).restrictScalars ℚ_[p]) = ⊤) :
    ∃ T : Subrepresentation ρ, Module.finrank K (V ⧸ T.toSubmodule) = 1 ∧
      zeroWeightSpan (ι := ι) ((ρ.quotient T.toSubmodule
        T.apply_mem_toSubmodule).restrictScalars ℚ_[p]) = ⊤ :=
  exists_quotient_spanned_by_fixed_periods_of_algebraic_baseChange ι ρ hV
    (zeroWeightSpan_ne_top_of_injective_comparison p ι hF
      (ρ.restrictScalars ℚ_[p]) hinj hq hx hx0) hex

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- The fixed-period quotient descends with its actual kernel along any algebraic
coefficient extension, including non-Galois extensions. -/
theorem exists_descended_quotient_spanned_by_fixed_periods_of_algebraic
    [Algebra.IsAlgebraic K L] [Module ℚ_[p] V] [IsScalarTower ℚ_[p] K V]
    (ρ : Representation K G V) (hV : Module.finrank K V = 2)
    (hρ : zeroWeightSpan (ι := ι) (ρ.restrictScalars ℚ_[p]) ≠ ⊤)
    (S : Subrepresentation (ρ.baseChange L))
    (hS : Module.finrank L ((L ⊗[K] V) ⧸ S.toSubmodule) = 1)
    (hfixed : zeroWeightSpan (ι := ι) (((ρ.baseChange L).quotient S.toSubmodule
      S.apply_mem_toSubmodule).restrictScalars ℚ_[p]) = ⊤) :
    ∃ T : Subrepresentation ρ, Module.finrank K (V ⧸ T.toSubmodule) = 1 ∧
      T.baseChange L = S ∧
      zeroWeightSpan (ι := ι) ((ρ.quotient T.toSubmodule
        T.apply_mem_toSubmodule).restrictScalars ℚ_[p]) = ⊤ := by
  obtain ⟨T, hT, hspan⟩ := exists_quotient_spanned_by_fixed_periods_of_algebraic_baseChange
    ι ρ hV hρ ⟨S, hS, hfixed⟩
  have hdim : Module.finrank L ((L ⊗[K] V) ⧸ (T.baseChange L).toSubmodule) = 1 := by
    rw [← (Representation.quotientBaseChangeEquiv L T).toLinearEquiv.finrank_eq,
      Module.finrank_baseChange, hT]
  have hspanL : zeroWeightSpan (ι := ι) (((ρ.baseChange L).quotient
      (T.baseChange L).toSubmodule (T.baseChange L).apply_mem_toSubmodule).restrictScalars ℚ_[p]) = ⊤ := by
    apply (zeroWeightSpan_eq_top_iff (ι := ι)
      ((Representation.quotientBaseChangeEquiv L T).restrictScalars ℚ_[p])).mp
    exact zeroWeightSpan_baseChange_eq_top _ hspan
  refine ⟨T, hT, ?_, hspan⟩
  apply eq_of_quotients_spanned_by_fixed_periods (ι := ι) (ρ.baseChange L)
    (by rw [Module.finrank_baseChange, hV])
    (fun h => hρ (zeroWeightSpan_eq_top_of_baseChange ρ h))
    (T.baseChange L) S hdim hS hspanL hfixed

section ComparisonDescent

variable [Algebra.IsAlgebraic K L] [Module ℚ_[p] V] [IsScalarTower ℚ_[p] K V]
  {F : Type*} [Field F] [Algebra ℚ_[p] F] [Algebra F ℂ_[p]]
  [IsScalarTower ℚ_[p] F ℂ_[p]]
  (hF : ∀ (g : G) (a : F), PadicComplex.galoisEquiv p (ι g)
    (algebraMap F ℂ_[p] a) = algebraMap F ℂ_[p] a)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- A rank-one quotient with bijective comparison and only weight zero descends
along algebraic coefficients, retaining its actual kernel and comparison data. -/
theorem exists_descended_quotient_with_comparison
    (ρ : Representation K G V) (hV : Module.finrank K V = 2)
    (hρ : zeroWeightSpan (ι := ι) (ρ.restrictScalars ℚ_[p]) ≠ ⊤)
    (S : Subrepresentation (ρ.baseChange L))
    (hS : Module.finrank L ((L ⊗[K] V) ⧸ S.toSubmodule) = 1)
    (hbij : Function.Bijective (comparison p ι hF
      (((ρ.baseChange L).quotient S.toSubmodule S.apply_mem_toSubmodule).restrictScalars ℚ_[p])))
    (hweights : ∀ q : ℤ, q ≠ 0 → weightSpace p ι
      (((ρ.baseChange L).quotient S.toSubmodule S.apply_mem_toSubmodule).restrictScalars ℚ_[p]) q = ⊥) :
    ∃ T : Subrepresentation ρ, Module.finrank K (V ⧸ T.toSubmodule) = 1 ∧
      T.baseChange L = S ∧
      Function.Bijective (comparison p ι hF
        ((ρ.quotient T.toSubmodule T.apply_mem_toSubmodule).restrictScalars ℚ_[p])) ∧
      ∀ q : ℤ, q ≠ 0 → weightSpace p ι
        ((ρ.quotient T.toSubmodule T.apply_mem_toSubmodule).restrictScalars ℚ_[p]) q = ⊥ := by
  have hfixed := zeroWeightSpan_eq_top_of_surjective_comparison p ι hF _ hbij.2 hweights
  obtain ⟨T, hT, he, hspan⟩ :=
    exists_descended_quotient_spanned_by_fixed_periods_of_algebraic ι ρ hV hρ S hS hfixed
  subst S
  have hinj : Function.Injective (comparison p ι hF
      ((ρ.quotient T.toSubmodule T.apply_mem_toSubmodule).restrictScalars ℚ_[p])) := by
    apply comparison_injective_of_baseChange p ι hF (L := L)
    apply (comparison_injective_iff p ι hF
      ((Representation.quotientBaseChangeEquiv L T).restrictScalars ℚ_[p])).mpr
    exact hbij.1
  obtain ⟨hcomp, hzero⟩ :=
    (zeroWeightSpan_eq_top_iff_comparison_bijective_and_weights_zero p ι hF _ hinj).mp hspan
  exact ⟨T, hT, rfl, hcomp, hzero⟩

/-- A nonzero period of nonzero weight and injective comparison give descent
of an actual rank-one weight-zero quotient, with bijective comparison retained. -/
theorem exists_weight_zero_quotient_of_nonzero_period
    (ρ : Representation K G V) (hV : Module.finrank K V = 2)
    (hinj : Function.Injective (comparison p ι hF (ρ.restrictScalars ℚ_[p])))
    {q : ℤ} (hq : q ≠ 0) {x : ℂ_[p] ⊗[ℚ_[p]] V}
    (hx : x ∈ weightSpace p ι (ρ.restrictScalars ℚ_[p]) q) (hx0 : x ≠ 0)
    (S : Subrepresentation (ρ.baseChange L))
    (hS : Module.finrank L ((L ⊗[K] V) ⧸ S.toSubmodule) = 1)
    (hbij : Function.Bijective (comparison p ι hF
      (((ρ.baseChange L).quotient S.toSubmodule S.apply_mem_toSubmodule).restrictScalars ℚ_[p])))
    (hweights : ∀ q : ℤ, q ≠ 0 → weightSpace p ι
      (((ρ.baseChange L).quotient S.toSubmodule S.apply_mem_toSubmodule).restrictScalars ℚ_[p]) q = ⊥) :
    ∃ T : Subrepresentation ρ, Module.finrank K (V ⧸ T.toSubmodule) = 1 ∧
      T.baseChange L = S ∧
      Function.Bijective (comparison p ι hF
        ((ρ.quotient T.toSubmodule T.apply_mem_toSubmodule).restrictScalars ℚ_[p])) ∧
      ∀ q : ℤ, q ≠ 0 → weightSpace p ι
        ((ρ.quotient T.toSubmodule T.apply_mem_toSubmodule).restrictScalars ℚ_[p]) q = ⊥ :=
  exists_descended_quotient_with_comparison ι hF ρ hV
    (zeroWeightSpan_ne_top_of_injective_comparison p ι hF
      (ρ.restrictScalars ℚ_[p]) hinj hq hx hx0) S hS hbij hweights

end ComparisonDescent

end HodgeTate
