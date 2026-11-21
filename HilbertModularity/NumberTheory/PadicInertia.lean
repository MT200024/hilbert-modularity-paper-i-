/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.PadicGalois
public import Mathlib.RingTheory.Valuation.RamificationGroup
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Algebra.OpenSubgroup

/-! # Inertia of the actual algebraic p-adic closure

The valuation ring is the ring of elements of norm at most one in the fixed
`PadicAlgCl p`. Every automorphism over a field containing `ℚ_[p]` preserves
this ring. Its action on the actual residue field defines inertia, using
mathlib's valuation-subring inertia subgroup. The norm characterization is
the local arithmetic interface needed in [TripathiGoswami]. No theorem
about finite inertia of de Rham characters is assumed or proved here.
-/

@[expose] public noncomputable section

open scoped Pointwise

namespace PadicAlgCl

variable (p : ℕ) [Fact p.Prime]

/-- The valuation ring in the fixed algebraic closure of the p-adic field. -/
def integerRing : ValuationSubring (PadicAlgCl p) := (valued p).v.valuationSubring

/-- Integral algebraic p-adic elements are exactly those of norm at most one. -/
theorem mem_integerRing (x : PadicAlgCl p) : x ∈ integerRing p ↔ ‖x‖ ≤ 1 := by
  change ‖x‖₊ ≤ 1 ↔ ‖x‖ ≤ 1
  exact NNReal.coe_le_coe

/-- The maximal ideal of the actual valuation ring consists of elements of norm less than one. -/
theorem mem_maximalIdeal_integerRing (x : integerRing p) :
    x ∈ IsLocalRing.maximalIdeal (integerRing p) ↔ ‖(x : PadicAlgCl p)‖ < 1 :=
  (Valuation.mem_maximalIdeal_iff (PadicAlgCl p) ((valued p).v) (a := x)).trans NNReal.coe_lt_coe


variable (K : Type*) [Field K] [Algebra ℚ_[p] K] [Algebra K (PadicAlgCl p)]
  [IsScalarTower ℚ_[p] K (PadicAlgCl p)]

/-- Automorphisms over any embedded extension of the p-adic base field preserve the actual norm. -/
theorem norm_galois_over (g : PadicAlgCl p ≃ₐ[K] PadicAlgCl p) (x : PadicAlgCl p) :
    ‖g x‖ = ‖x‖ := norm_galois p (g.restrictScalars ℚ_[p]) x

/-- Every actual local Galois automorphism belongs to the valuation-ring decomposition subgroup. -/
def galoisDecomposition : (PadicAlgCl p ≃ₐ[K] PadicAlgCl p) →*
    (integerRing p).decompositionSubgroup K where
  toFun g := ⟨g, by
    change g • integerRing p = integerRing p
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, mem_integerRing, mem_integerRing]
    change ‖g⁻¹ x‖ ≤ 1 ↔ ‖x‖ ≤ 1
    rw [norm_galois_over p K]⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

/-- The actual Galois action restricted to the valuation ring. -/
def integerAction : (PadicAlgCl p ≃ₐ[K] PadicAlgCl p) →* RingAut (integerRing p) :=
  (MulSemiringAction.toRingAut ((integerRing p).decompositionSubgroup K)
    (integerRing p)).comp (galoisDecomposition p K)

/-- Restriction to the integer ring retains the original field automorphism. -/
@[simp] theorem integerAction_apply (g : PadicAlgCl p ≃ₐ[K] PadicAlgCl p) (x : integerRing p) :
    (integerAction p K g x : PadicAlgCl p) = g (x : PadicAlgCl p) := rfl

/-- The action on the residue field of the actual algebraic p-adic valuation ring. -/
def residueAction : (PadicAlgCl p ≃ₐ[K] PadicAlgCl p) →*
    RingAut (IsLocalRing.ResidueField (integerRing p)) :=
  (MulSemiringAction.toRingAut ((integerRing p).decompositionSubgroup K)
    (IsLocalRing.ResidueField (integerRing p))).comp (galoisDecomposition p K)

/-- The residue action is induced by the actual action on integral elements. -/
@[simp] theorem residueAction_residue (g : PadicAlgCl p ≃ₐ[K] PadicAlgCl p)
    (x : integerRing p) :
    residueAction p K g (IsLocalRing.residue (integerRing p) x) =
      IsLocalRing.residue (integerRing p) (integerAction p K g x) := rfl

/-- Actual p-adic inertia, pulled back from the native valuation-subring inertia group. -/
def inertia : Subgroup (PadicAlgCl p ≃ₐ[K] PadicAlgCl p) :=
  ((integerRing p).inertiaSubgroup K).comap (galoisDecomposition p K)

/-- Actual inertia is exactly the kernel of the action on the actual residue field. -/
theorem inertia_eq_ker_residueAction : inertia p K = (residueAction p K).ker := rfl

/-- Inertia acts trivially on the residues of all actual integral elements. -/
theorem mem_inertia_iff_residue (g : PadicAlgCl p ≃ₐ[K] PadicAlgCl p) :
    g ∈ inertia p K ↔ ∀ x : integerRing p,
      IsLocalRing.residue (integerRing p) (integerAction p K g x) =
        IsLocalRing.residue (integerRing p) x := by
  change residueAction p K g = 1 ↔ _
  constructor
  · intro h x
    rw [← residueAction_residue, h]
    rfl
  · intro h
    apply RingEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    exact h x

/-- The classical norm test for inertia uses the original field action on integral elements. -/
theorem mem_inertia_iff_norm (g : PadicAlgCl p ≃ₐ[K] PadicAlgCl p) :
    g ∈ inertia p K ↔ ∀ x : PadicAlgCl p, ‖x‖ ≤ 1 → ‖g x - x‖ < 1 := by
  rw [mem_inertia_iff_residue]
  have h (x : integerRing p) :
      IsLocalRing.residue (integerRing p) (integerAction p K g x) =
        IsLocalRing.residue (integerRing p) x ↔ ‖g (x : PadicAlgCl p) - x‖ < 1 := by
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
      mem_maximalIdeal_integerRing]
    rfl
  simp_rw [h]
  exact Subtype.forall.trans (by simp only [mem_integerRing])

/-- Changing the embedded base field does not change the norm test for inertia. -/
theorem mem_inertia_restrictScalars (g : PadicAlgCl p ≃ₐ[K] PadicAlgCl p) :
    g.restrictScalars ℚ_[p] ∈ inertia p ℚ_[p] ↔ g ∈ inertia p K := by
  rw [mem_inertia_iff_norm, mem_inertia_iff_norm]
  rfl

/-- Inertia over an embedded local field is the inverse image of p-adic absolute inertia. -/
theorem inertia_eq_comap_restrictScalars :
    inertia p K = (inertia p ℚ_[p]).comap (AlgEquiv.restrictScalarsHom ℚ_[p]) := by
  ext g
  exact (mem_inertia_restrictScalars p K g).symm

/-- The original algebraic orbit maps are locally constant in the actual Krull topology. -/
theorem isLocallyConstant_galois_over (x : PadicAlgCl p) :
    IsLocallyConstant (fun g : PadicAlgCl p ≃ₐ[K] PadicAlgCl p => g x) := by
  let : Algebra.IsIntegral K (PadicAlgCl p) := Algebra.IsIntegral.tower_top ℚ_[p]
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro g
  have ho := (stabilizer_isOpen_of_isIntegral (K := K) x).preimage
    (continuous_const.mul continuous_id : Continuous fun h => g⁻¹ * h)
  have hn := ho.mem_nhds (show g⁻¹ * g ∈
    MulAction.stabilizer (PadicAlgCl p ≃ₐ[K] PadicAlgCl p) x by simp)
  filter_upwards [hn] with h hh
  change (g⁻¹ * h) x = x at hh
  have := congrArg g hh
  simpa using this

/-- The integral orbit maps retain local constancy of the actual field action. -/
theorem isLocallyConstant_integerAction (x : integerRing p) :
    IsLocallyConstant (fun g : PadicAlgCl p ≃ₐ[K] PadicAlgCl p => integerAction p K g x) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro g
  filter_upwards [(isLocallyConstant_galois_over p K (x : PadicAlgCl p)).eventually_eq g] with h hh
  exact Subtype.ext hh

/-- Every residue orbit is locally constant for the actual Krull topology. -/
theorem isLocallyConstant_residueAction (x : IsLocalRing.ResidueField (integerRing p)) :
    IsLocallyConstant (fun g : PadicAlgCl p ≃ₐ[K] PadicAlgCl p => residueAction p K g x) := by
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
  exact (isLocallyConstant_integerAction p K y).comp (IsLocalRing.residue (integerRing p))

/-- Actual p-adic inertia is closed in the Krull topology. -/
theorem isClosed_inertia : IsClosed (inertia p K : Set (PadicAlgCl p ≃ₐ[K] PadicAlgCl p)) := by
  have h : (inertia p K : Set (PadicAlgCl p ≃ₐ[K] PadicAlgCl p)) =
      ⋂ x : integerRing p, {g | IsLocalRing.residue (integerRing p) (integerAction p K g x) =
        IsLocalRing.residue (integerRing p) x} := by
    ext g
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, SetLike.mem_coe, mem_inertia_iff_residue]
  rw [h]
  apply isClosed_iInter
  intro x
  exact ((isLocallyConstant_integerAction p K x).comp
    (IsLocalRing.residue (integerRing p))).isClosed_fiber _

/-- Actual p-adic inertia is a normal subgroup, as the kernel of its residue action. -/
instance inertia_normal : (inertia p K).Normal := by
  rw [inertia_eq_ker_residueAction]
  infer_instance

/-- Inertia of an intermediate p-adic field maps to the intersection with its actual fixing subgroup. -/
theorem map_inertia_restrictScalars (F : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    (inertia p F).map (AlgEquiv.restrictScalarsHom ℚ_[p]) =
      inertia p ℚ_[p] ⊓ F.fixingSubgroup := by
  ext g
  constructor
  · rintro ⟨h, hh, rfl⟩
    refine ⟨(mem_inertia_restrictScalars p F h).mpr hh, ?_⟩
    apply (IntermediateField.mem_fixingSubgroup_iff F _).mpr
    intro x hx
    exact h.commutes ⟨x, hx⟩
  · rintro ⟨hg, hfix⟩
    refine ⟨F.fixingSubgroupEquiv ⟨g, hfix⟩, ?_, ?_⟩
    · exact (mem_inertia_restrictScalars p F _).mp hg
    · ext x
      rfl

/-- Restriction of scalars embeds actual local inertia into p-adic absolute inertia. -/
def inertiaRestriction : inertia p K →* inertia p ℚ_[p] where
  toFun g := ⟨g.val.restrictScalars ℚ_[p], (mem_inertia_restrictScalars p K g.val).mpr g.property⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

/-- Restriction retains the full underlying automorphism of the fixed algebraic closure. -/
theorem inertiaRestriction_injective : Function.Injective (inertiaRestriction p K) := by
  intro g h e
  apply Subtype.ext
  ext x
  exact congrArg (fun σ : inertia p ℚ_[p] => σ.val x) e

/-- The image of local inertia is exactly the subgroup fixing the chosen intermediate field. -/
theorem range_inertiaRestriction (F : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    (inertiaRestriction p F).range = F.fixingSubgroup.comap (inertia p ℚ_[p]).subtype := by
  ext g
  constructor
  · rintro ⟨h, rfl⟩
    apply (IntermediateField.mem_fixingSubgroup_iff F _).mpr
    intro x hx
    exact h.val.commutes ⟨x, hx⟩
  · intro hfix
    refine ⟨⟨F.fixingSubgroupEquiv ⟨g.val, hfix⟩, ?_⟩, ?_⟩
    · exact (mem_inertia_restrictScalars p F _).mp g.property
    · apply Subtype.ext
      ext x
      rfl

/-- For a finite embedded local extension, its inertia image is open in p-adic absolute inertia. -/
theorem isOpen_range_inertiaRestriction
    (F : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] F] :
    IsOpen ((inertiaRestriction p F).range : Set (inertia p ℚ_[p])) := by
  rw [range_inertiaRestriction]
  exact (IntermediateField.fixingSubgroup_isOpen F).preimage continuous_subtype_val

/-- Actual inertia is compact as a closed subgroup of the actual profinite Galois group. -/
theorem isCompact_inertia : IsCompact (inertia p K : Set (PadicAlgCl p ≃ₐ[K] PadicAlgCl p)) := by
  let : IsGalois K (PadicAlgCl p) := IsGalois.tower_top_of_isGalois ℚ_[p] K (PadicAlgCl p)
  exact (isClosed_inertia p K).isCompact

/-- The actual inertia subgroup has its compact subspace topology. -/
instance inertia_compactSpace : CompactSpace (inertia p K) :=
  isCompact_iff_compactSpace.mp (isCompact_inertia p K)

/-- The inertia image of a finite embedded local extension has finite index in absolute inertia. -/
theorem finiteIndex_range_inertiaRestriction
    (F : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] F] :
    (inertiaRestriction p F).range.FiniteIndex := by
  have : Finite (inertia p ℚ_[p] ⧸ (inertiaRestriction p F).range) :=
    Subgroup.quotient_finite_of_isOpen _ (isOpen_range_inertiaRestriction p F)
  exact Subgroup.finiteIndex_of_finite_quotient

/-- The image of inertia fixes exactly the image of the specified local-field embedding. -/
theorem range_inertiaRestriction_fieldRange :
    (inertiaRestriction p K).range =
      (IsScalarTower.toAlgHom ℚ_[p] K (PadicAlgCl p)).fieldRange.fixingSubgroup.comap
        (inertia p ℚ_[p]).subtype := by
  ext g
  constructor
  · rintro ⟨h, rfl⟩
    apply (IntermediateField.mem_fixingSubgroup_iff _ _).mpr
    rintro x ⟨y, rfl⟩
    exact h.val.commutes y
  · intro hfix
    let h : PadicAlgCl p ≃ₐ[K] PadicAlgCl p :=
      { g.val.toRingEquiv with
        commutes' := fun x =>
          (IntermediateField.mem_fixingSubgroup_iff _ _).mp hfix
            (algebraMap K (PadicAlgCl p) x) ⟨x, rfl⟩ }
    refine ⟨⟨h, ?_⟩, ?_⟩
    · exact (mem_inertia_restrictScalars p K h).mp g.property
    · apply Subtype.ext
      ext x
      rfl

/-- For any finite local field with its specified embedding, the inertia image is open. -/
theorem isOpen_range_inertiaRestriction_of_finite [FiniteDimensional ℚ_[p] K] :
    IsOpen ((inertiaRestriction p K).range : Set (inertia p ℚ_[p])) := by
  let f := IsScalarTower.toAlgHom ℚ_[p] K (PadicAlgCl p)
  let : FiniteDimensional ℚ_[p] f.fieldRange :=
    Module.Finite.of_surjective f.equivFieldRange.toLinearMap f.equivFieldRange.surjective
  rw [range_inertiaRestriction_fieldRange]
  exact (IntermediateField.fixingSubgroup_isOpen f.fieldRange).preimage continuous_subtype_val

/-- Actual inertia of any finite embedded local field has finite-index image. -/
theorem finiteIndex_range_inertiaRestriction_of_finite [FiniteDimensional ℚ_[p] K] :
    (inertiaRestriction p K).range.FiniteIndex := by
  have : Finite (inertia p ℚ_[p] ⧸ (inertiaRestriction p K).range) :=
    Subgroup.quotient_finite_of_isOpen _ (isOpen_range_inertiaRestriction_of_finite p K)
  exact Subgroup.finiteIndex_of_finite_quotient

open scoped Topology in
/-- Restriction of actual algebraic p-adic automorphisms is continuous for the Krull topologies. -/
theorem continuous_restrictScalars :
    Continuous (AlgEquiv.restrictScalarsHom ℚ_[p] :
      (PadicAlgCl p ≃ₐ[K] PadicAlgCl p) →* (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)) := by
  apply continuous_of_tendsto_nhds_one
  intro s hs
  obtain ⟨F, hF, hFs⟩ := (krullTopology_mem_nhds_one_iff ℚ_[p] (PadicAlgCl p) s).mp hs
  let := hF
  let b := Module.Basis.ofVectorSpace ℚ_[p] F
  have h : ∀ᶠ g : PadicAlgCl p ≃ₐ[K] PadicAlgCl p in 𝓝 1,
      ∀ i, g ((b i : F) : PadicAlgCl p) = ((b i : F) : PadicAlgCl p) :=
    Filter.eventually_all.mpr fun i => (isLocallyConstant_galois_over p K _).eventually_eq 1
  change ∀ᶠ g : PadicAlgCl p ≃ₐ[K] PadicAlgCl p in 𝓝 1, g.restrictScalars ℚ_[p] ∈ s
  filter_upwards [h] with g hg
  apply hFs
  apply (IntermediateField.mem_fixingSubgroup_iff F _).mpr
  intro x hx
  have he : (g.restrictScalars ℚ_[p]).toAlgHom.toLinearMap.comp F.val.toLinearMap =
      F.val.toLinearMap := b.ext hg
  exact congrArg (fun f : F →ₗ[ℚ_[p]] PadicAlgCl p => f ⟨x, hx⟩) he

/-- The actual inertia restriction homomorphism is continuous in the subgroup topologies. -/
theorem continuous_inertiaRestriction : Continuous (inertiaRestriction p K) :=
  ((continuous_restrictScalars p K).comp continuous_subtype_val).subtype_mk _

/-- Actual inertia restriction identifies the source with a closed subgroup of absolute inertia. -/
theorem isClosedEmbedding_inertiaRestriction :
    Topology.IsClosedEmbedding (inertiaRestriction p K) :=
  (continuous_inertiaRestriction p K).isClosedEmbedding (inertiaRestriction_injective p K)

/-- A finite local extension identifies its actual inertia with an open subgroup of absolute inertia. -/
theorem isOpenEmbedding_inertiaRestriction [FiniteDimensional ℚ_[p] K] :
    Topology.IsOpenEmbedding (inertiaRestriction p K) :=
  ⟨(isClosedEmbedding_inertiaRestriction p K).isEmbedding,
    isOpen_range_inertiaRestriction_of_finite p K⟩

/-- Algebraic p-adic integers represent all completed integers modulo elements of norm less than one. -/
theorem exists_integer_approximation (x : ℂ_[p]) (hx : ‖x‖ ≤ 1) :
    ∃ y : PadicAlgCl p, ‖y‖ ≤ 1 ∧ dist x (y : ℂ_[p]) < 1 := by
  obtain ⟨y, hy⟩ := Metric.denseRange_iff.mp
    (UniformSpace.Completion.denseRange_coe (α := PadicAlgCl p)) x 1 zero_lt_one
  refine ⟨y, ?_, hy⟩
  rw [← PadicComplex.norm_extends, ← dist_zero_right]
  exact (dist_triangle_max (y : ℂ_[p]) x 0).trans
    (max_le (by simpa only [dist_comm] using hy.le) (by simpa only [dist_zero_right] using hx))

/-- Actual inertia is equally detected by the completed p-adic action on all integral elements. -/
theorem mem_inertia_iff_completed_norm (g : PadicAlgCl p ≃ₐ[K] PadicAlgCl p) :
    g ∈ inertia p K ↔ ∀ x : ℂ_[p], ‖x‖ ≤ 1 →
      ‖PadicComplex.galoisEquiv p (g.restrictScalars ℚ_[p]) x - x‖ < 1 := by
  rw [mem_inertia_iff_norm]
  constructor
  · intro hg x hx
    obtain ⟨y, hy, hxy⟩ := exists_integer_approximation p x hx
    let σ := PadicComplex.galoisEquiv p (g.restrictScalars ℚ_[p])
    have hyy : dist (σ (y : ℂ_[p])) (y : ℂ_[p]) < 1 := by
      simpa only [σ, PadicComplex.galoisEquiv_coe, AlgEquiv.restrictScalars_apply,
        dist_eq_norm, ← UniformSpace.Completion.coe_sub, PadicComplex.norm_extends] using hg y hy
    have hσ : dist (σ x) (σ (y : ℂ_[p])) < 1 := by
      rw [(PadicComplex.isometry_galoisEquiv p (g.restrictScalars ℚ_[p])).dist_eq]
      exact hxy
    rw [← dist_eq_norm]
    exact (dist_triangle_max (σ x) (σ (y : ℂ_[p])) x).trans_lt
      (max_lt hσ ((dist_triangle_max (σ (y : ℂ_[p])) (y : ℂ_[p]) x).trans_lt
        (max_lt hyy (by simpa only [dist_comm] using hxy))))
  · intro hg x hx
    have h := hg (x : ℂ_[p]) (by simpa only [PadicComplex.norm_extends] using hx)
    simpa only [PadicComplex.galoisEquiv_coe, AlgEquiv.restrictScalars_apply,
      ← UniformSpace.Completion.coe_sub,
      PadicComplex.norm_extends] using h

end PadicAlgCl
