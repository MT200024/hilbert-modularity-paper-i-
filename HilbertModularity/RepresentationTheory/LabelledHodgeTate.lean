/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.Descent
public import HilbertModularity.RepresentationTheory.HodgeTateComparison
public import HilbertModularity.RepresentationTheory.CoefficientPeriodTwist
public import HilbertModularity.LinearAlgebra.CoefficientDecomposition
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! # Coefficient-labelled Hodge–Tate spaces

Local-field labels arise by extending the coefficient field and splitting the
action of the local base field on the actual Hodge–Tate period spaces. The local
base and coefficient fields are kept separate, including when their underlying
types happen to agree. This supplies the labelled weight-zero criterion used in
[TripathiGoswami].
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace CompleteOrthogonalIdempotents

variable {R M I : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [Fintype I] {e : I → Module.End R M}

/-- Every labelled projection vanishes exactly when the whole module is zero. -/
theorem forall_range_eq_bot_iff_subsingleton (he : CompleteOrthogonalIdempotents e) :
    (∀ i, LinearMap.range (e i) = ⊥) ↔ Subsingleton M := by
  constructor
  · intro h
    refine ⟨fun x y => he.linearEquiv.injective ?_⟩
    ext i
    have hz (z : LinearMap.range (e i)) : (z : M) = 0 := by
      have hm := z.property
      simpa [h i] using hm
    exact (hz _).trans (hz _).symm
  · intro h i
    let : Subsingleton M := h
    exact Subsingleton.elim _ _

end CompleteOrthogonalIdempotents

namespace Algebra.TensorProduct

variable {F K E D : Type*} [Field F] [Field K] [Field E]
  [Algebra F K] [Algebra F E] [AddCommGroup D] [Module E D]
  [Module F D] [IsScalarTower F E D]

/-- Extending the coefficient field extends a commuting local-field action to its split tensor. -/
def scalarExtensionAction (α : K →ₐ[F] Module.End E D) :
    AlgebraicClosure E ⊗[F] K →ₐ[AlgebraicClosure E]
      Module.End (AlgebraicClosure E) (AlgebraicClosure E ⊗[E] D) :=
  Algebra.TensorProduct.lift (Algebra.ofId (AlgebraicClosure E) _)
    (((Module.End.baseChangeHom E (AlgebraicClosure E) D).restrictScalars F).comp α)
    (fun c _ => Algebra.commutes c _)

@[simp]
theorem scalarExtensionAction_tmul (α : K →ₐ[F] Module.End E D)
    (c d : AlgebraicClosure E) (a : K) (x : D) :
    scalarExtensionAction α (c ⊗ₜ[F] a) (d ⊗ₜ[E] x) =
      (c * d) ⊗ₜ[E] α a x := by
  change c • (d ⊗ₜ[E] α a x) = _
  rw [TensorProduct.smul_tmul']
  rfl

variable [FiniteDimensional F K] [Algebra.IsSeparable F K]

/-- The canonical projection associated with a local-field embedding after coefficient extension. -/
def scalarExtensionEmbeddingProjection (α : K →ₐ[F] Module.End E D)
    (τ : K →ₐ[F] AlgebraicClosure E) :
    Module.End (AlgebraicClosure E) (AlgebraicClosure E ⊗[E] D) :=
  scalarExtensionAction α
    (embeddingIdempotent F K (AlgebraicClosure E) (fun _ => IsAlgClosed.splits _) τ)

/-- These canonical labelled projections form a complete orthogonal family. -/
theorem completeOrthogonalIdempotents_scalarExtensionEmbeddingProjection
    (α : K →ₐ[F] Module.End E D) :
    CompleteOrthogonalIdempotents (scalarExtensionEmbeddingProjection α) :=
  (completeOrthogonalIdempotents_embeddingIdempotent F K (AlgebraicClosure E)
    (fun _ => IsAlgClosed.splits _)).map (scalarExtensionAction α).toRingHom


/-- On a canonical labelled factor, the local field acts through its specified embedding. -/
theorem scalarExtensionAction_on_embeddingProjection
    (α : K →ₐ[F] Module.End E D) (τ : K →ₐ[F] AlgebraicClosure E)
    (c : AlgebraicClosure E) (a : K)
    (v : LinearMap.range (scalarExtensionEmbeddingProjection α τ)) :
    scalarExtensionAction α (c ⊗ₜ[F] a) (v : AlgebraicClosure E ⊗[E] D) =
      (c * τ a) • (v : AlgebraicClosure E ⊗[E] D) := by
  obtain ⟨w, hw⟩ := v.property
  change scalarExtensionAction α
    (embeddingIdempotent F K (AlgebraicClosure E) (fun _ => IsAlgClosed.splits _) τ) w = v at hw
  rw [← hw]
  change (scalarExtensionAction α (c ⊗ₜ[F] a) * scalarExtensionAction α
    (embeddingIdempotent F K (AlgebraicClosure E) (fun _ => IsAlgClosed.splits _) τ)) w = _
  rw [← map_mul, tmul_mul_embeddingIdempotent, map_smul]
  rfl

/-- All labelled pieces vanish exactly when the original coefficient module vanishes. -/
theorem forall_scalarExtensionEmbeddingProjection_range_eq_bot_iff
    (α : K →ₐ[F] Module.End E D) :
    (∀ τ, LinearMap.range (scalarExtensionEmbeddingProjection α τ) = ⊥) ↔
      Subsingleton D := by
  rw [(completeOrthogonalIdempotents_scalarExtensionEmbeddingProjection α).forall_range_eq_bot_iff_subsingleton]
  exact Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right E (AlgebraicClosure E)

end Algebra.TensorProduct

namespace HodgeTate

variable (p : ℕ) [Fact p.Prime]
  {K E G V : Type*} [Field K] [Field E] [Algebra ℚ_[p] K] [Algebra ℚ_[p] E]
  [Algebra K ℂ_[p]] [IsScalarTower ℚ_[p] K ℂ_[p]]
  [Group G] [AddCommGroup V] [Module E V] [Module ℚ_[p] V]
  [IsScalarTower ℚ_[p] E V]
  (ι : G →* (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p))
  (hK : ∀ (g : G) (a : K), PadicComplex.galoisEquiv p (ι g)
    (algebraMap K ℂ_[p] a) = algebraMap K ℂ_[p] a)

/-- The coefficient field acts on the right tensor factor of the actual completed period space. -/
def coefficientEndAction : E →ₐ[ℚ_[p]] Module.End ℂ_[p] (ℂ_[p] ⊗[ℚ_[p]] V) :=
  ((periodCoefficientAction p).restrictScalars ℚ_[p]).comp Algebra.TensorProduct.includeRight

/-- Coefficient multiplication preserves the actual cyclotomic eigenspaces. -/
theorem coefficientEndAction_mem_weightSpace (ρ : Representation E G V) (q : ℤ)
    (a : E) (x : ℂ_[p] ⊗[ℚ_[p]] V)
    (hx : x ∈ weightSpace p ι (ρ.restrictScalars ℚ_[p]) q) :
    coefficientEndAction p a x ∈ weightSpace p ι (ρ.restrictScalars ℚ_[p]) q := by
  rw [mem_weightSpace] at hx ⊢
  intro g
  change periodRepresentation p ι (ρ.restrictScalars ℚ_[p]) g
    (periodCoefficientAction p ((1 : ℂ_[p]) ⊗ₜ[ℚ_[p]] a) x) = _
  rw [periodRepresentation_coefficientAction]
  have hg : periodCoefficientGalois p ι g ((1 : ℂ_[p]) ⊗ₜ[ℚ_[p]] a) =
      (1 : ℂ_[p]) ⊗ₜ[ℚ_[p]] a := by simp [periodCoefficientGalois]
  rw [hg, hx g]
  exact (periodCoefficientAction p ((1 : ℂ_[p]) ⊗ₜ[ℚ_[p]] a)).map_smul_of_tower _ _

/-- The coefficient field acts on a concrete local Hodge–Tate space, commuting with the local base. -/
def localWeightSpaceCoefficientAction (ρ : Representation E G V) (q : ℤ) :
    E →ₐ[ℚ_[p]] Module.End K (localWeightSpace p ι hK (ρ.restrictScalars ℚ_[p]) q) where
  toFun a := ((coefficientEndAction p a).restrictScalars K).restrict
    (fun x hx => coefficientEndAction_mem_weightSpace p ι ρ q a x hx)
  map_zero' := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun f : Module.End ℂ_[p] (ℂ_[p] ⊗[ℚ_[p]] V) => f x)
      (map_zero (coefficientEndAction p))
  map_one' := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun f : Module.End ℂ_[p] (ℂ_[p] ⊗[ℚ_[p]] V) => f x)
      (map_one (coefficientEndAction p))
  map_add' a b := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun f : Module.End ℂ_[p] (ℂ_[p] ⊗[ℚ_[p]] V) => f x)
      (map_add (coefficientEndAction p) a b)
  map_mul' a b := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun f : Module.End ℂ_[p] (ℂ_[p] ⊗[ℚ_[p]] V) => f x)
      (map_mul (coefficientEndAction p) a b)
  commutes' r := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun f : Module.End ℂ_[p] (ℂ_[p] ⊗[ℚ_[p]] V) => f x)
      ((coefficientEndAction p).commutes r)

/-- The actual local weight space equipped with its coefficient-field module structure.
The type alias keeps coefficient and local-base actions distinct when the fields coincide. -/
def coefficientWeightSpace (ρ : Representation E G V) (q : ℤ) : Type _ :=
  localWeightSpace p ι hK (ρ.restrictScalars ℚ_[p]) q

instance instAddCommGroupCoefficientWeightSpace (ρ : Representation E G V) (q : ℤ) :
    AddCommGroup (coefficientWeightSpace p ι hK ρ q) :=
  inferInstanceAs (AddCommGroup (localWeightSpace p ι hK (ρ.restrictScalars ℚ_[p]) q))

instance instModuleCoefficientWeightSpace (ρ : Representation E G V) (q : ℤ) :
    Module E (coefficientWeightSpace p ι hK ρ q) :=
  Module.compHom (localWeightSpace p ι hK (ρ.restrictScalars ℚ_[p]) q)
    (localWeightSpaceCoefficientAction p ι hK ρ q).toRingHom

instance (priority := 900) instModuleRationalCoefficientWeightSpace (ρ : Representation E G V) (q : ℤ) :
    Module ℚ_[p] (coefficientWeightSpace p ι hK ρ q) :=
  Module.compHom _ (algebraMap ℚ_[p] E)

instance instScalarTowerCoefficientWeightSpace (ρ : Representation E G V) (q : ℤ) :
    IsScalarTower ℚ_[p] E (coefficientWeightSpace p ι hK ρ q) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

/-- Forgetting the coefficient structure recovers exactly the original concrete weight space. -/
def coefficientWeightSpaceEquiv (ρ : Representation E G V) (q : ℤ) :
    coefficientWeightSpace p ι hK ρ q ≃+ localWeightSpace p ι hK (ρ.restrictScalars ℚ_[p]) q :=
  AddEquiv.refl _

/-- The local base field acts coefficient-linearly on the same actual weight space. -/
def coefficientWeightSpaceLocalAction (ρ : Representation E G V) (q : ℤ) :
    K →ₐ[ℚ_[p]] Module.End E (coefficientWeightSpace p ι hK ρ q) where
  toFun a :=
    { toFun x := a • (show localWeightSpace p ι hK (ρ.restrictScalars ℚ_[p]) q from x)
      map_add' x y := smul_add a (show localWeightSpace p ι hK (ρ.restrictScalars ℚ_[p]) q from x) (show localWeightSpace p ι hK (ρ.restrictScalars ℚ_[p]) q from y)
      map_smul' e x := by
        change a • (localWeightSpaceCoefficientAction p ι hK ρ q e x) =
          localWeightSpaceCoefficientAction p ι hK ρ q e (a • (show localWeightSpace p ι hK (ρ.restrictScalars ℚ_[p]) q from x))
        exact ((localWeightSpaceCoefficientAction p ι hK ρ q e).map_smul a (show localWeightSpace p ι hK (ρ.restrictScalars ℚ_[p]) q from x)).symm }
  map_zero' := by
    apply LinearMap.ext
    intro x
    exact zero_smul K (show localWeightSpace p ι hK (ρ.restrictScalars ℚ_[p]) q from x)
  map_one' := by
    apply LinearMap.ext
    intro x
    exact one_smul K (show localWeightSpace p ι hK (ρ.restrictScalars ℚ_[p]) q from x)
  map_add' a b := by
    apply LinearMap.ext
    intro x
    exact add_smul a b (show localWeightSpace p ι hK (ρ.restrictScalars ℚ_[p]) q from x)
  map_mul' a b := by
    apply LinearMap.ext
    intro x
    exact mul_smul a b (show localWeightSpace p ι hK (ρ.restrictScalars ℚ_[p]) q from x)
  commutes' r := by
    apply LinearMap.ext
    intro x
    change (algebraMap ℚ_[p] K r) • (show localWeightSpace p ι hK (ρ.restrictScalars ℚ_[p]) q from x) =
      localWeightSpaceCoefficientAction p ι hK ρ q (algebraMap ℚ_[p] E r) x
    rw [(localWeightSpaceCoefficientAction p ι hK ρ q).commutes]
    exact algebraMap_smul K r (show localWeightSpace p ι hK (ρ.restrictScalars ℚ_[p]) q from x)

variable [FiniteDimensional ℚ_[p] K]

/-- The actual weight `q` space labelled by a local-field embedding, after coefficient extension. -/
def labelledWeightSpace (ρ : Representation E G V) (q : ℤ)
    (τ : K →ₐ[ℚ_[p]] AlgebraicClosure E) :
    Submodule (AlgebraicClosure E)
      (AlgebraicClosure E ⊗[E] coefficientWeightSpace p ι hK ρ q) :=
  LinearMap.range (Algebra.TensorProduct.scalarExtensionEmbeddingProjection
    (coefficientWeightSpaceLocalAction p ι hK ρ q) τ)

/-- The canonical decomposition into the actual local-field-labelled weight spaces. -/
def labelledWeightSpaceDecomposition (ρ : Representation E G V) (q : ℤ) :
    (AlgebraicClosure E ⊗[E] coefficientWeightSpace p ι hK ρ q) ≃ₗ[AlgebraicClosure E]
      ((τ : K →ₐ[ℚ_[p]] AlgebraicClosure E) → labelledWeightSpace p ι hK ρ q τ) :=
  (Algebra.TensorProduct.completeOrthogonalIdempotents_scalarExtensionEmbeddingProjection
    (coefficientWeightSpaceLocalAction p ι hK ρ q)).linearEquiv

/-- The local field acts on the labelled weight space through the displayed local embedding. -/
theorem labelledWeightSpace_localField_action (ρ : Representation E G V) (q : ℤ)
    (τ : K →ₐ[ℚ_[p]] AlgebraicClosure E) (a : K)
    (v : labelledWeightSpace p ι hK ρ q τ) :
    Algebra.TensorProduct.scalarExtensionAction (coefficientWeightSpaceLocalAction p ι hK ρ q)
      ((1 : AlgebraicClosure E) ⊗ₜ[ℚ_[p]] a)
      (v : AlgebraicClosure E ⊗[E] coefficientWeightSpace p ι hK ρ q) =
      τ a • (v : AlgebraicClosure E ⊗[E] coefficientWeightSpace p ι hK ρ q) := by
  simpa using Algebra.TensorProduct.scalarExtensionAction_on_embeddingProjection
    (coefficientWeightSpaceLocalAction p ι hK ρ q) τ 1 a v

/-- Vanishing at every genuine local-field label is exactly vanishing of the actual eigenspace. -/
theorem forall_labelledWeightSpace_eq_bot_iff (ρ : Representation E G V) (q : ℤ) :
    (∀ τ, labelledWeightSpace p ι hK ρ q τ = ⊥) ↔
      weightSpace p ι (ρ.restrictScalars ℚ_[p]) q = ⊥ := by
  change (∀ τ, LinearMap.range (Algebra.TensorProduct.scalarExtensionEmbeddingProjection
    (coefficientWeightSpaceLocalAction p ι hK ρ q) τ) = ⊥) ↔ _
  rw [Algebra.TensorProduct.forall_scalarExtensionEmbeddingProjection_range_eq_bot_iff,
    ← Submodule.subsingleton_iff_eq_bot]
  exact (coefficientWeightSpaceEquiv p ι hK ρ q).toEquiv.subsingleton_congr

/-- All local labels have only weight zero exactly when every nonzero actual eigenspace vanishes. -/
theorem all_labelled_weights_zero_iff (ρ : Representation E G V) :
    (∀ τ, ∀ q : ℤ, q ≠ 0 → labelledWeightSpace p ι hK ρ q τ = ⊥) ↔
      ∀ q : ℤ, q ≠ 0 → weightSpace p ι (ρ.restrictScalars ℚ_[p]) q = ⊥ := by
  rw [forall_comm]
  apply forall_congr'
  intro q
  rw [forall_comm]
  exact forall_congr' fun _ => forall_labelledWeightSpace_eq_bot_iff p ι hK ρ q

/-- The canonical comparison criterion with labelled weights equals its unlabelled formulation. -/
theorem comparison_and_labelled_weights_zero_iff (ρ : Representation E G V) :
    (Function.Bijective (comparison p ι hK (ρ.restrictScalars ℚ_[p])) ∧
      ∀ τ, ∀ q : ℤ, q ≠ 0 → labelledWeightSpace p ι hK ρ q τ = ⊥) ↔
    (Function.Bijective (comparison p ι hK (ρ.restrictScalars ℚ_[p])) ∧
      ∀ q : ℤ, q ≠ 0 → weightSpace p ι (ρ.restrictScalars ℚ_[p]) q = ⊥) :=
  and_congr Iff.rfl (all_labelled_weights_zero_iff p ι hK ρ)

/-- The labelled and unlabelled actual comparison criteria select the same rank-one quotients. -/
theorem exists_labelled_weight_zero_quotient_iff (ρ : Representation E G V) :
    (∃ S : Subrepresentation ρ, Module.finrank E (V ⧸ S.toSubmodule) = 1 ∧
      Function.Bijective (comparison p ι hK
        ((ρ.quotient S.toSubmodule S.apply_mem_toSubmodule).restrictScalars ℚ_[p])) ∧
      ∀ τ, ∀ q : ℤ, q ≠ 0 → labelledWeightSpace p ι hK
        (ρ.quotient S.toSubmodule S.apply_mem_toSubmodule) q τ = ⊥) ↔
    ∃ S : Subrepresentation ρ, Module.finrank E (V ⧸ S.toSubmodule) = 1 ∧
      Function.Bijective (comparison p ι hK
        ((ρ.quotient S.toSubmodule S.apply_mem_toSubmodule).restrictScalars ℚ_[p])) ∧
      ∀ q : ℤ, q ≠ 0 → weightSpace p ι
        ((ρ.quotient S.toSubmodule S.apply_mem_toSubmodule).restrictScalars ℚ_[p]) q = ⊥ := by
  exact exists_congr fun S => and_congr Iff.rfl
    (comparison_and_labelled_weights_zero_iff p ι hK
      (ρ.quotient S.toSubmodule S.apply_mem_toSubmodule))

/-- All-labelled weight vanishing and actual eigenspace vanishing select the same rank-one quotients. -/
theorem exists_quotient_labelled_weights_zero_iff (ρ : Representation E G V) :
    (∃ S : Subrepresentation ρ, Module.finrank E (V ⧸ S.toSubmodule) = 1 ∧
      ∀ τ, ∀ q : ℤ, q ≠ 0 → labelledWeightSpace p ι hK
        (ρ.quotient S.toSubmodule S.apply_mem_toSubmodule) q τ = ⊥) ↔
    ∃ S : Subrepresentation ρ, Module.finrank E (V ⧸ S.toSubmodule) = 1 ∧
      ∀ q : ℤ, q ≠ 0 → weightSpace p ι
        ((ρ.quotient S.toSubmodule S.apply_mem_toSubmodule).restrictScalars ℚ_[p]) q = ⊥ := by
  exact exists_congr fun S => and_congr Iff.rfl
    (all_labelled_weights_zero_iff p ι hK
      (ρ.quotient S.toSubmodule S.apply_mem_toSubmodule))

/-- A nonzero genuine labelled factor yields a nonzero period in the actual weight eigenspace. -/
theorem exists_nonzero_period_of_labelledWeightSpace_ne_bot
    (ρ : Representation E G V) (q : ℤ) (τ : K →ₐ[ℚ_[p]] AlgebraicClosure E)
    (hτ : labelledWeightSpace p ι hK ρ q τ ≠ ⊥) :
    ∃ x ∈ weightSpace p ι (ρ.restrictScalars ℚ_[p]) q, x ≠ 0 := by
  apply (Submodule.ne_bot_iff _).mp
  intro h
  exact hτ ((forall_labelledWeightSpace_eq_bot_iff p ι hK ρ q).mpr h τ)

omit [FiniteDimensional ℚ_[p] K] in
/-- Injectivity of the actual comparison makes every local weight space finite dimensional. -/
theorem finiteDimensional_localWeightSpace_of_comparison_injective
    [FiniteDimensional ℚ_[p] V] (ρ : Representation E G V)
    (hinj : Function.Injective (comparison p ι hK (ρ.restrictScalars ℚ_[p]))) (q : ℤ) :
    FiniteDimensional K (localWeightSpace p ι hK (ρ.restrictScalars ℚ_[p]) q) := by
  have hi : Function.Injective (weightComparison p ι hK (ρ.restrictScalars ℚ_[p]) q) := by
    intro x y h
    have he := hinj (show comparison p ι hK (ρ.restrictScalars ℚ_[p])
        (DirectSum.lof ℂ_[p] ℤ _ q x) =
        comparison p ι hK (ρ.restrictScalars ℚ_[p]) (DirectSum.lof ℂ_[p] ℤ _ q y) by
      simpa only [comparison_lof] using h)
    have hv := congrArg (fun z => z q) he
    simpa [DirectSum.lof_eq_of, DirectSum.of_apply] using hv
  let : FiniteDimensional ℂ_[p]
      (ℂ_[p] ⊗[K] localWeightSpace p ι hK (ρ.restrictScalars ℚ_[p]) q) :=
    FiniteDimensional.of_injective (weightComparison p ι hK (ρ.restrictScalars ℚ_[p]) q) hi
  rw [FiniteDimensional, ← Module.rank_lt_aleph0_iff]
  have h := Module.rank_lt_aleph0_iff.mpr
    (inferInstance : Module.Finite ℂ_[p]
      (ℂ_[p] ⊗[K] localWeightSpace p ι hK (ρ.restrictScalars ℚ_[p]) q))
  simpa [Module.rank_baseChange] using h

omit [FiniteDimensional ℚ_[p] K] in
/-- The coefficient and local-base structures induce the same rational scalar action. -/
def coefficientWeightSpaceRestrictScalarsEquiv (ρ : Representation E G V) (q : ℤ) :
    coefficientWeightSpace p ι hK ρ q ≃ₗ[ℚ_[p]]
      localWeightSpace p ι hK (ρ.restrictScalars ℚ_[p]) q where
  __ := coefficientWeightSpaceEquiv p ι hK ρ q
  map_smul' r x := by
    change localWeightSpaceCoefficientAction p ι hK ρ q (algebraMap ℚ_[p] E r) x = r • (show localWeightSpace p ι hK (ρ.restrictScalars ℚ_[p]) q from x)
    rw [(localWeightSpaceCoefficientAction p ι hK ρ q).commutes]
    rfl

/-- Actual coefficient weight spaces are finite dimensional under injective comparison. -/
theorem finiteDimensional_coefficientWeightSpace_of_comparison_injective
    [FiniteDimensional ℚ_[p] V] (ρ : Representation E G V)
    (hinj : Function.Injective (comparison p ι hK (ρ.restrictScalars ℚ_[p]))) (q : ℤ) :
    FiniteDimensional E (coefficientWeightSpace p ι hK ρ q) := by
  let := finiteDimensional_localWeightSpace_of_comparison_injective p ι hK ρ hinj q
  let : FiniteDimensional ℚ_[p] (localWeightSpace p ι hK (ρ.restrictScalars ℚ_[p]) q) :=
    Module.Finite.trans K _
  let e := coefficientWeightSpaceRestrictScalarsEquiv p ι hK ρ q
  let : FiniteDimensional ℚ_[p] (coefficientWeightSpace p ι hK ρ q) :=
    FiniteDimensional.of_injective e.toLinearMap e.injective
  exact Module.Finite.right ℚ_[p] E _

/-- Every actual labelled weight space has finite dimension under injective comparison. -/
theorem finiteDimensional_labelledWeightSpace_of_comparison_injective
    [FiniteDimensional ℚ_[p] V] (ρ : Representation E G V)
    (hinj : Function.Injective (comparison p ι hK (ρ.restrictScalars ℚ_[p]))) (q : ℤ)
    (τ : K →ₐ[ℚ_[p]] AlgebraicClosure E) :
    FiniteDimensional (AlgebraicClosure E) (labelledWeightSpace p ι hK ρ q τ) := by
  let := finiteDimensional_coefficientWeightSpace_of_comparison_injective p ι hK ρ hinj q
  infer_instance

/-- Vanishing of genuine finite labelled multiplicities is exactly vanishing of the actual weight. -/
theorem forall_labelledWeightSpace_finrank_eq_zero_iff
    [FiniteDimensional ℚ_[p] V] (ρ : Representation E G V)
    (hinj : Function.Injective (comparison p ι hK (ρ.restrictScalars ℚ_[p]))) (q : ℤ) :
    (∀ τ, Module.finrank (AlgebraicClosure E) (labelledWeightSpace p ι hK ρ q τ) = 0) ↔
      weightSpace p ι (ρ.restrictScalars ℚ_[p]) q = ⊥ := by
  refine Iff.trans (forall_congr' fun τ => ?_)
    (forall_labelledWeightSpace_eq_bot_iff p ι hK ρ q)
  let := finiteDimensional_labelledWeightSpace_of_comparison_injective p ι hK ρ hinj q τ
  exact Submodule.finrank_eq_zero

section LabelledDescent

variable {L : Type*} [Field L] [Algebra E L] [Algebra ℚ_[p] L]
  [IsScalarTower ℚ_[p] E L] [Algebra.IsAlgebraic E L] [FiniteDimensional E V]

/-- Actual labelled weight-zero quotients descend along algebraic coefficients, retaining their
kernel and canonical comparison, when the original representation has a nonzero labelled weight. -/
theorem exists_descended_labelled_weight_zero_quotient
    (ρ : Representation E G V) (hV : Module.finrank E V = 2)
    (hinj : Function.Injective (comparison p ι hK (ρ.restrictScalars ℚ_[p])))
    {q : ℤ} (hq : q ≠ 0) (τ : K →ₐ[ℚ_[p]] AlgebraicClosure E)
    (hτ : labelledWeightSpace p ι hK ρ q τ ≠ ⊥)
    (S : Subrepresentation (ρ.baseChange L))
    (hS : Module.finrank L ((L ⊗[E] V) ⧸ S.toSubmodule) = 1)
    (hbij : Function.Bijective (comparison p ι hK
      (((ρ.baseChange L).quotient S.toSubmodule S.apply_mem_toSubmodule).restrictScalars ℚ_[p])))
    (hweights : ∀ σ, ∀ n : ℤ, n ≠ 0 → labelledWeightSpace p ι hK
      ((ρ.baseChange L).quotient S.toSubmodule S.apply_mem_toSubmodule) n σ = ⊥) :
    ∃ T : Subrepresentation ρ, Module.finrank E (V ⧸ T.toSubmodule) = 1 ∧
      T.baseChange L = S ∧
      Function.Bijective (comparison p ι hK
        ((ρ.quotient T.toSubmodule T.apply_mem_toSubmodule).restrictScalars ℚ_[p])) ∧
      ∀ σ, ∀ n : ℤ, n ≠ 0 → labelledWeightSpace p ι hK
        (ρ.quotient T.toSubmodule T.apply_mem_toSubmodule) n σ = ⊥ := by
  obtain ⟨x, hx, hx0⟩ := exists_nonzero_period_of_labelledWeightSpace_ne_bot p ι hK ρ q τ hτ
  obtain ⟨T, hT, he, hcomp, hw⟩ := exists_weight_zero_quotient_of_nonzero_period ι hK
    ρ hV hinj hq hx hx0 S hS hbij
    ((all_labelled_weights_zero_iff p ι hK _).mp hweights)
  exact ⟨T, hT, he, hcomp, (all_labelled_weights_zero_iff p ι hK _).mpr hw⟩

end LabelledDescent

end HodgeTate
