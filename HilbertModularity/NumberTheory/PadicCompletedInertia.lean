/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.PadicInertia

/-! # Inertia and the residue field of the completed p-adic closure

The actual completed Galois action preserves the native `PadicComplexInt`.
Its residue action has exactly the algebraic inertia subgroup as kernel.
This connects the local inertia used in [TripathiGoswami] with the
completed field used for Hodge–Tate periods; no finite-image theorem is assumed.
-/

@[expose] public noncomputable section

open scoped Pointwise

namespace PadicComplex

variable (p : ℕ) [Fact p.Prime]

/-- The native completed valuation is the nonnegative norm of the completed p-adic field. -/
theorem valuation_eq_nnnorm (x : ℂ_[p]) : (valued p).v x = ‖x‖₊ := by
  apply NNReal.coe_injective
  simpa only [Valuation.norm_def, RankOne.hom_eq_embedding,
    Valuation.embedding_restrict, coe_nnnorm] using (norm_eq_norm p x).symm

/-- The native completed integer ring consists exactly of the elements of norm at most one. -/
theorem mem_integerRing (x : ℂ_[p]) : x ∈ PadicComplexInt p ↔ ‖x‖ ≤ 1 := by
  change (valued p).v x ≤ 1 ↔ ‖x‖ ≤ 1
  rw [valuation_eq_nnnorm]
  exact NNReal.coe_le_coe

/-- The native completed maximal ideal consists of the elements of norm less than one. -/
theorem mem_maximalIdeal_integerRing (x : PadicComplexInt p) :
    x ∈ IsLocalRing.maximalIdeal (PadicComplexInt p) ↔ ‖(x : ℂ_[p])‖ < 1 := by
  exact (Valuation.mem_maximalIdeal_iff ℂ_[p] ((valued p).v) (a := x)).trans
    ((by rw [valuation_eq_nnnorm] : (valued p).v (x : ℂ_[p]) < 1 ↔ ‖(x : ℂ_[p])‖₊ < 1).trans
      NNReal.coe_lt_coe)

/-- The actual completion embedding restricts to the native integer rings. -/
def integerCompletion : PadicAlgCl.integerRing p →+* PadicComplexInt p where
  toFun x := ⟨(x.val : ℂ_[p]), (mem_integerRing p _).mpr
    (by rw [norm_extends]; exact (PadicAlgCl.mem_integerRing p _).mp x.property)⟩
  map_zero' := Subtype.ext (UniformSpace.Completion.coe_zero)
  map_one' := Subtype.ext (UniformSpace.Completion.coe_one (PadicAlgCl p))
  map_add' x y := Subtype.ext (UniformSpace.Completion.coe_add x.val y.val)
  map_mul' x y := Subtype.ext (UniformSpace.Completion.coe_mul x.val y.val)

/-- Restriction to integers retains the actual completion embedding. -/
@[simp] theorem integerCompletion_apply (x : PadicAlgCl.integerRing p) :
    (integerCompletion p x : ℂ_[p]) = (x.val : ℂ_[p]) := rfl

/-- The completion embedding of integer rings is a local homomorphism. -/
instance integerCompletion_isLocalHom : IsLocalHom (integerCompletion p) where
  map_nonunit x hx := by
    by_contra hn
    have h : integerCompletion p x ∈ IsLocalRing.maximalIdeal (PadicComplexInt p) := by
      rw [mem_maximalIdeal_integerRing, integerCompletion_apply, norm_extends]
      exact (PadicAlgCl.mem_maximalIdeal_integerRing p x).mp hn
    exact h hx

/-- The residue homomorphism induced by the actual completion embedding is surjective. -/
theorem residueMap_integerCompletion_surjective :
    Function.Surjective (IsLocalRing.ResidueField.map (integerCompletion p)) := by
  intro z
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
  obtain ⟨y, hy, hxy⟩ := PadicAlgCl.exists_integer_approximation p (x : ℂ_[p])
    ((mem_integerRing p _).mp x.property)
  refine ⟨IsLocalRing.residue (PadicAlgCl.integerRing p)
    ⟨y, (PadicAlgCl.mem_integerRing p y).mpr hy⟩, ?_⟩
  rw [IsLocalRing.ResidueField.map_residue]
  apply sub_eq_zero.mp
  rw [← map_sub, IsLocalRing.residue_eq_zero_iff, mem_maximalIdeal_integerRing]
  change ‖(y : ℂ_[p]) - x‖ < 1
  simpa only [← dist_eq_norm, dist_comm] using hxy

/-- Completion preserves the actual p-adic residue field. -/
def residueCompletionEquiv : IsLocalRing.ResidueField (PadicAlgCl.integerRing p) ≃+*
    IsLocalRing.ResidueField (PadicComplexInt p) :=
  RingEquiv.ofBijective (IsLocalRing.ResidueField.map (integerCompletion p))
    ⟨(IsLocalRing.ResidueField.map (integerCompletion p)).injective,
      residueMap_integerCompletion_surjective p⟩

/-- The residue equivalence sends an algebraic integral representative to its actual completion. -/
@[simp] theorem residueCompletionEquiv_residue (x : PadicAlgCl.integerRing p) :
    residueCompletionEquiv p (IsLocalRing.residue (PadicAlgCl.integerRing p) x) =
      IsLocalRing.residue (PadicComplexInt p) (integerCompletion p x) :=
  IsLocalRing.ResidueField.map_residue (integerCompletion p) x

variable (K : Type*) [Field K] [Algebra ℚ_[p] K] [Algebra K (PadicAlgCl p)]
  [IsScalarTower ℚ_[p] K (PadicAlgCl p)]

/-- Every completed local Galois action preserves the native completed integer ring. -/
def galoisDecomposition : (PadicAlgCl p ≃ₐ[K] PadicAlgCl p) →*
    (PadicComplexInt p).decompositionSubgroup ℚ_[p] where
  toFun g := ⟨galoisEquiv p (g.restrictScalars ℚ_[p]), by
    change galoisEquiv p (g.restrictScalars ℚ_[p]) • PadicComplexInt p = PadicComplexInt p
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, mem_integerRing, mem_integerRing]
    have h := (isometry_galoisEquiv p (g.restrictScalars ℚ_[p])).dist_eq
      ((galoisEquiv p (g.restrictScalars ℚ_[p]))⁻¹ x) 0
    have hn : ‖(galoisEquiv p (g.restrictScalars ℚ_[p]))⁻¹ x‖ = ‖x‖ := by
      simpa only [dist_zero_right, map_zero, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply] using h.symm
    exact Iff.of_eq (congrArg (fun r : ℝ => r ≤ 1) hn)⟩
  map_one' := Subtype.ext (galoisEquiv_one p)
  map_mul' g h := Subtype.ext (galoisEquiv_mul p (g.restrictScalars ℚ_[p]) (h.restrictScalars ℚ_[p]))

/-- The actual completed action on its native integer ring. -/
def integerAction : (PadicAlgCl p ≃ₐ[K] PadicAlgCl p) →* RingAut (PadicComplexInt p) :=
  (MulSemiringAction.toRingAut ((PadicComplexInt p).decompositionSubgroup ℚ_[p])
    (PadicComplexInt p)).comp (galoisDecomposition p K)

/-- The completed integral action is the restriction of the actual completed field action. -/
@[simp] theorem integerAction_apply (g : PadicAlgCl p ≃ₐ[K] PadicAlgCl p)
    (x : PadicComplexInt p) :
    (integerAction p K g x : ℂ_[p]) = galoisEquiv p (g.restrictScalars ℚ_[p]) x := rfl

/-- The actual completed residue-field action of the local Galois group. -/
def residueAction : (PadicAlgCl p ≃ₐ[K] PadicAlgCl p) →*
    RingAut (IsLocalRing.ResidueField (PadicComplexInt p)) :=
  (MulSemiringAction.toRingAut ((PadicComplexInt p).decompositionSubgroup ℚ_[p])
    (IsLocalRing.ResidueField (PadicComplexInt p))).comp (galoisDecomposition p K)

/-- Reduction intertwines the native completed integral action and its residue action. -/
@[simp] theorem residueAction_residue (g : PadicAlgCl p ≃ₐ[K] PadicAlgCl p)
    (x : PadicComplexInt p) :
    residueAction p K g (IsLocalRing.residue (PadicComplexInt p) x) =
      IsLocalRing.residue (PadicComplexInt p) (integerAction p K g x) := rfl

/-- The completed residue action is trivial exactly on the actual algebraic inertia subgroup. -/
theorem inertia_eq_ker_residueAction : PadicAlgCl.inertia p K = (residueAction p K).ker := by
  ext g
  rw [PadicAlgCl.mem_inertia_iff_completed_norm]
  change (∀ x : ℂ_[p], ‖x‖ ≤ 1 → ‖galoisEquiv p (g.restrictScalars ℚ_[p]) x - x‖ < 1) ↔
    residueAction p K g = 1
  have hr : residueAction p K g = 1 ↔ ∀ x : PadicComplexInt p,
      IsLocalRing.residue (PadicComplexInt p) (integerAction p K g x) =
        IsLocalRing.residue (PadicComplexInt p) x := by
    constructor
    · intro h x
      rw [← residueAction_residue, h]
      rfl
    · intro h
      apply RingEquiv.ext
      intro y
      obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
      exact h x
  rw [hr]
  have h (x : PadicComplexInt p) :
      IsLocalRing.residue (PadicComplexInt p) (integerAction p K g x) =
        IsLocalRing.residue (PadicComplexInt p) x ↔
      ‖galoisEquiv p (g.restrictScalars ℚ_[p]) (x : ℂ_[p]) - x‖ < 1 := by
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
      mem_maximalIdeal_integerRing]
    rfl
  simp_rw [h]
  exact (Subtype.forall.trans (by simp only [mem_integerRing])).symm

/-- The actual integer-ring completion map intertwines the algebraic and completed actions. -/
theorem integerCompletion_integerAction (g : PadicAlgCl p ≃ₐ[K] PadicAlgCl p)
    (x : PadicAlgCl.integerRing p) :
    integerCompletion p (PadicAlgCl.integerAction p K g x) =
      integerAction p K g (integerCompletion p x) := by
  apply Subtype.ext
  simp only [integerCompletion_apply, PadicAlgCl.integerAction_apply,
    integerAction_apply, galoisEquiv_coe, AlgEquiv.restrictScalars_apply]

/-- The canonical residue-field equivalence is equivariant for the actual local Galois actions. -/
theorem residueCompletionEquiv_equivariant (g : PadicAlgCl p ≃ₐ[K] PadicAlgCl p)
    (x : IsLocalRing.ResidueField (PadicAlgCl.integerRing p)) :
    residueCompletionEquiv p (PadicAlgCl.residueAction p K g x) =
      residueAction p K g (residueCompletionEquiv p x) := by
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
  rw [PadicAlgCl.residueAction_residue, residueCompletionEquiv_residue,
    residueCompletionEquiv_residue, residueAction_residue, integerCompletion_integerAction]

/-- Every completed residue orbit is locally constant for the actual Krull topology. -/
theorem isLocallyConstant_residueAction (x : IsLocalRing.ResidueField (PadicComplexInt p)) :
    IsLocallyConstant (fun g : PadicAlgCl p ≃ₐ[K] PadicAlgCl p => residueAction p K g x) := by
  obtain ⟨y, rfl⟩ := (residueCompletionEquiv p).surjective x
  have h := (PadicAlgCl.isLocallyConstant_residueAction p K y).comp (residueCompletionEquiv p)
  simpa only [Function.comp_def, residueCompletionEquiv_equivariant] using h

end PadicComplex
