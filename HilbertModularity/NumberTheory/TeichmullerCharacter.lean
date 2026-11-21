/- Assembled by AxiomProver. -/

module

public import Mathlib.RingTheory.Teichmuller
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.FieldTheory.Perfect
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.Ring.Compact
public import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic

/-! # Teichmüller lifts of residual characters

The canonical multiplicative lift over an adically complete coefficient ring
splits reduction on units. Dividing a unit-valued character by the lift of its
reduction gives a character in the actual kernel of reduction, as used in
[TripathiGoswami].
-/

@[expose] public noncomputable section

namespace Ideal

variable {R : Type*} [CommRing R] (I : Ideal R) (p : ℕ) [Fact p.Prime]
  [CharP (R ⧸ I) p] [PerfectRing (R ⧸ I) p] [IsAdicComplete I R]

/-- The canonical Teichmüller lift from a perfect residue ring. -/
def teichmullerLift : (R ⧸ I) →* R :=
  (Perfection.teichmuller p I).comp
    ((Perfection.lift p (R ⧸ I) (R ⧸ I)) (RingHom.id _)).toMonoidHom

/-- The canonical lift is a multiplicative section of reduction. -/
@[simp]
theorem quotient_mk_teichmullerLift (x : R ⧸ I) :
    Ideal.Quotient.mk I (teichmullerLift I p x) = x := by
  simp only [teichmullerLift, MonoidHom.comp_apply,
    Perfection.mk_teichmuller]
  rfl

/-- The induced Teichmüller lift of residue units. -/
def teichmullerUnits : (R ⧸ I)ˣ →* Rˣ :=
  Units.map (teichmullerLift I p)

/-- Reduction of the canonical lifted residue unit is the original unit. -/
@[simp]
theorem reduction_teichmullerUnits (x : (R ⧸ I)ˣ) :
    Units.map (Ideal.Quotient.mk I : R →* R ⧸ I) (teichmullerUnits I p x) = x := by
  apply Units.ext
  exact quotient_mk_teichmullerLift I p x

variable {G : Type*} [Group G]

/-- The actual Teichmüller lift of a residual unit-valued character. -/
def teichmullerCharacter (χ : G →* (R ⧸ I)ˣ) : G →* Rˣ :=
  (teichmullerUnits I p).comp χ

/-- The Teichmüller character has exactly the prescribed reduction. -/
@[simp]
theorem reduction_teichmullerCharacter (χ : G →* (R ⧸ I)ˣ) (g : G) :
    Units.map (Ideal.Quotient.mk I : R →* R ⧸ I) (teichmullerCharacter I p χ g) = χ g :=
  reduction_teichmullerUnits I p (χ g)

/-- Divide an integral unit-valued character by the canonical lift of its reduction. -/
def teichmullerNormalizedCharacter (ψ : G →* Rˣ) : G →* Rˣ :=
  ψ * (teichmullerCharacter I p
    ((Units.map (Ideal.Quotient.mk I : R →* R ⧸ I)).comp ψ))⁻¹

/-- The normalized character lies in the actual principal-unit kernel. -/
@[simp]
theorem reduction_teichmullerNormalizedCharacter (ψ : G →* Rˣ) (g : G) :
    Units.map (Ideal.Quotient.mk I : R →* R ⧸ I)
      (teichmullerNormalizedCharacter I p ψ g) = 1 := by
  change Units.map (Ideal.Quotient.mk I : R →* R ⧸ I) (ψ g) *
    (Units.map (Ideal.Quotient.mk I : R →* R ⧸ I)
      (teichmullerCharacter I p ((Units.map (Ideal.Quotient.mk I : R →* R ⧸ I)).comp ψ) g))⁻¹ = 1
  rw [reduction_teichmullerCharacter]
  simp

/-- The normalized character takes values in the actual kernel of reduction on units. -/
def principalUnitCharacter (ψ : G →* Rˣ) :
    G →* (Units.map (Ideal.Quotient.mk I : R →* R ⧸ I)).ker :=
  (teichmullerNormalizedCharacter I p ψ).codRestrict _ fun g =>
    reduction_teichmullerNormalizedCharacter I p ψ g

/-- The lift of a residual character has finite order bounded by the residue-unit group. -/
theorem teichmullerCharacter_pow_card (χ : G →* (R ⧸ I)ˣ) :
    teichmullerCharacter I p χ ^ Nat.card (R ⧸ I)ˣ = 1 := by
  apply MonoidHom.ext
  intro g
  change teichmullerUnits I p (χ g) ^ Nat.card (R ⧸ I)ˣ = 1
  rw [← map_pow, pow_card_eq_one', map_one]

/-- A finite residue ring makes the canonical lifted character finite order. -/
theorem isOfFinOrder_teichmullerCharacter [Finite (R ⧸ I)]
    (χ : G →* (R ⧸ I)ˣ) : IsOfFinOrder (teichmullerCharacter I p χ) :=
  isOfFinOrder_iff_pow_eq_one.mpr
    ⟨Nat.card (R ⧸ I)ˣ, Nat.card_pos, teichmullerCharacter_pow_card I p χ⟩

/-- A residual character over a finite residue ring has a finite Teichmüller image. -/
theorem finite_range_teichmullerCharacter [Finite (R ⧸ I)]
    (χ : G →* (R ⧸ I)ˣ) : (Set.range (teichmullerCharacter I p χ)).Finite := by
  apply (Set.finite_range (teichmullerUnits I p)).subset
  rintro _ ⟨g, rfl⟩
  exact ⟨χ g, rfl⟩

/-- Continuity of the residual character gives continuity of its canonical lift. -/
theorem continuous_teichmullerCharacter
    [TopologicalSpace R] [TopologicalSpace (R ⧸ I)] [DiscreteTopology (R ⧸ I)]
    [TopologicalSpace G] (χ : G →* (R ⧸ I)ˣ) (hχ : Continuous χ) :
    Continuous (teichmullerCharacter I p χ) := by
  change Continuous ((teichmullerUnits I p) ∘ χ)
  exact (continuous_of_discreteTopology : Continuous (teichmullerUnits I p)).comp hχ

/-- Normalization preserves continuity when the actual residue ring is discrete. -/
theorem continuous_teichmullerNormalizedCharacter
    [TopologicalSpace R] [IsTopologicalRing R] [DiscreteTopology (R ⧸ I)]
    [TopologicalSpace G] (ψ : G →* Rˣ) (hψ : Continuous ψ) :
    Continuous (teichmullerNormalizedCharacter I p ψ) := by
  have hr : Continuous (Units.map (Ideal.Quotient.mk I : R →* R ⧸ I)) :=
    Continuous.units_map _ continuous_quot_mk
  have hres : Continuous (fun g => Units.map (Ideal.Quotient.mk I : R →* R ⧸ I) (ψ g)) :=
    hr.comp hψ
  exact hψ.mul (continuous_teichmullerCharacter I p
    ((Units.map (Ideal.Quotient.mk I : R →* R ⧸ I)).comp ψ) hres).inv

/-- A compact source gives a compact actual image of the normalized character. -/
theorem isCompact_range_teichmullerNormalizedCharacter
    [TopologicalSpace R] [IsTopologicalRing R] [DiscreteTopology (R ⧸ I)]
    [TopologicalSpace G] [CompactSpace G] (ψ : G →* Rˣ) (hψ : Continuous ψ) :
    IsCompact (Set.range (teichmullerNormalizedCharacter I p ψ)) :=
  isCompact_range (continuous_teichmullerNormalizedCharacter I p ψ hψ)

/-- A finite image stays finite after Teichmüller normalization. This is the elementary step
used after the separate finite-inertia theorem has supplied finite image on inertia. -/
theorem finite_range_teichmullerNormalizedCharacter [Finite (R ⧸ I)]
    (ψ : G →* Rˣ) (hψ : (Set.range ψ).Finite) :
    (Set.range (teichmullerNormalizedCharacter I p ψ)).Finite := by
  let χ := (Units.map (Ideal.Quotient.mk I : R →* R ⧸ I)).comp ψ
  have ht := finite_range_teichmullerCharacter I p χ
  apply (hψ.mul ht.inv).subset
  rintro _ ⟨g, rfl⟩
  exact Set.mul_mem_mul (Set.mem_range_self g)
    (Set.mem_inv.mpr (Set.mem_range_self g))

/-- Finite image on a specified subgroup is preserved by normalization; this applies to inertia
after finite inertia of the original weight-zero character has been supplied. -/
theorem finite_range_teichmullerNormalizedCharacter_comp [Finite (R ⧸ I)]
    {H : Type*} [Group H] (i : H →* G) (ψ : G →* Rˣ)
    (hψ : (Set.range (ψ.comp i)).Finite) :
    (Set.range ((teichmullerNormalizedCharacter I p ψ).comp i)).Finite := by
  exact finite_range_teichmullerNormalizedCharacter I p (ψ.comp i) hψ

end Ideal


namespace IsNonarchimedeanLocalField

open scoped ValuativeRel

variable (K : Type*) [Field K] [ValuativeRel K] [UniformSpace K]
  [IsUniformAddGroup K] [IsNonarchimedeanLocalField K]
  (p : ℕ) [Fact p.Prime] [CharP (𝒪[K] ⧸ 𝓂[K]) p]
  {G : Type*} [Group G]

/-- The canonical lift of a residual character over the actual integers of a local field. -/
def teichmullerCharacter (χ : G →* (𝒪[K] ⧸ 𝓂[K])ˣ) : G →* 𝒪[K]ˣ :=
  letI : Finite (𝒪[K] ⧸ 𝓂[K]) := inferInstanceAs (Finite 𝓀[K])
  Ideal.teichmullerCharacter 𝓂[K] p χ

/-- Normalize an integral local-field character using its actual residue character. -/
def normalizedCharacter (ψ : G →* 𝒪[K]ˣ) : G →* 𝒪[K]ˣ :=
  letI : Finite (𝒪[K] ⧸ 𝓂[K]) := inferInstanceAs (Finite 𝓀[K])
  Ideal.teichmullerNormalizedCharacter 𝓂[K] p ψ

/-- The normalized local-field character reduces to one. -/
theorem reduction_normalizedCharacter (ψ : G →* 𝒪[K]ˣ) (g : G) :
    Units.map (IsLocalRing.residue 𝒪[K] : 𝒪[K] →* 𝓀[K])
      (normalizedCharacter K p ψ g) = 1 :=
  letI : Finite (𝒪[K] ⧸ 𝓂[K]) := inferInstanceAs (Finite 𝓀[K])
  Ideal.reduction_teichmullerNormalizedCharacter 𝓂[K] p ψ g

end IsNonarchimedeanLocalField

namespace Ideal

open Filter Topology
open scoped SModEq

variable {R : Type*} [CommRing R] (I : Ideal R) (p : ℕ)
  [CharP (R ⧸ I) p]

/-- Successive p-powering of a principal unit tends to one in the actual adic topology. -/
theorem tendsto_pow_pow_of_quotient_eq_one [TopologicalSpace R] (hI : IsAdic I)
    {x : R} (hx : Ideal.Quotient.mk I x = 1) :
    Tendsto (fun n : ℕ => x ^ p ^ n) atTop (𝓝 1) := by
  apply (hI.hasBasis_nhds 1).tendsto_right_iff.mpr
  intro m _
  filter_upwards [eventually_ge_atTop m] with n hn
  have h : x ≡ 1 [SMOD I] := SModEq.idealQuotientMk.mpr (by simpa using hx)
  have hp := h.pow_pow_add_one (I.natCast_mem_of_charP_quotient p) n
  rw [one_pow, SModEq.sub_mem] at hp
  refine ⟨x ^ p ^ n - 1, Ideal.pow_le_pow_right (by omega) hp, ?_⟩
  simp

/-- The p-power sequence of a principal unit converges to one in the unit-group topology. -/
theorem tendsto_units_pow_pow_of_reduction_eq_one [TopologicalSpace R] (hI : IsAdic I)
    (u : Rˣ) (hu : Units.map (Ideal.Quotient.mk I : R →* R ⧸ I) u = 1) :
    Tendsto (fun n : ℕ => u ^ p ^ n) atTop (𝓝 1) := by
  have hval : Ideal.Quotient.mk I (u : R) = 1 := congrArg Units.val hu
  have hinv : Ideal.Quotient.mk I (↑u⁻¹ : R) = 1 := by
    have h := congrArg (fun v : (R ⧸ I)ˣ => (↑v⁻¹ : R ⧸ I)) hu
    simpa using h
  apply Units.isInducing_embedProduct.tendsto_nhds_iff.mpr
  have hv := tendsto_pow_pow_of_quotient_eq_one I p hI hval
  have hi := tendsto_pow_pow_of_quotient_eq_one I p hI hinv
  simpa [Function.comp_def, Units.embedProduct_apply, nhds_prod_eq] using
    hv.prodMk (MulOpposite.continuous_op.tendsto 1 |>.comp hi)

/-- Principal-unit p-powers converge in the principal-unit subgroup itself. -/
theorem tendsto_principalUnit_pow_pow [TopologicalSpace R] (hI : IsAdic I)
    (u : (Units.map (Ideal.Quotient.mk I : R →* R ⧸ I)).ker) :
    Tendsto (fun n : ℕ => u ^ p ^ n) atTop (𝓝 1) := by
  apply tendsto_subtype_rng.mpr
  exact tendsto_units_pow_pow_of_reduction_eq_one I p hI u u.property

/-- Every discrete continuous image of the principal units is a p-group. In particular, this
proves the finite-quotient condition in the pro-p property without assuming it as a premise. -/
theorem isPGroup_range_of_continuous_principalUnit_hom
    [TopologicalSpace R] (hI : IsAdic I)
    {H : Type*} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    (f : (Units.map (Ideal.Quotient.mk I : R →* R ⧸ I)).ker →* H) (hf : Continuous f) :
    IsPGroup p f.range := by
  rw [isPGroup_iff_pow_pow_eq_one]
  rintro ⟨y, u, rfl⟩
  have h := hf.continuousAt.tendsto.comp (tendsto_principalUnit_pow_pow I p hI u)
  have he : ∀ᶠ n : ℕ in atTop, f (u ^ p ^ n) = 1 := by
    simpa only [map_one, nhds_discrete, tendsto_pure, Function.comp_def] using h
  obtain ⟨n, hn⟩ := he.exists
  refine ⟨n, Subtype.ext ?_⟩
  simpa only [Subgroup.coe_pow, MonoidHom.mem_range, Subgroup.coe_one, map_pow] using hn


end Ideal


namespace IsLocalRing

open Filter Topology

/-- A compact Hausdorff Noetherian local ring separated for its maximal ideal has its actual
maximal-ideal-adic topology. -/
theorem isAdic_maximalIdeal_of_compact
    (R : Type*) [CommRing R] [IsLocalRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [CompactSpace R] [T2Space R] [IsNoetherianRing R]
    [IsHausdorff (maximalIdeal R) R] : IsAdic (maximalIdeal R) := by
  rw [isAdic_iff]
  refine ⟨isOpen_maximalIdeal_pow R, fun U hU => ?_⟩
  have hi : (⨅ n : ℕ, maximalIdeal R ^ n : Ideal R) = ⊥ := by
    simpa using IsHausdorff.iInf_pow_smul (inferInstance : IsHausdorff (maximalIdeal R) R)
  have hs : (⋂ n : ℕ, ((maximalIdeal R ^ n : Ideal R) : Set R)) = {0} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_singleton_iff, SetLike.mem_coe]
    rw [← Submodule.mem_iInf, hi, Submodule.mem_bot]
  apply exists_subset_nhds_of_compactSpace
    (V := fun n : ℕ => ((maximalIdeal R ^ n : Ideal R) : Set R))
    (fun i j => ⟨max i j, Ideal.pow_le_pow_right (le_max_left _ _),
      Ideal.pow_le_pow_right (le_max_right _ _)⟩)
    (fun n => IsNoetherianRing.isClosed_ideal _) 
  simpa [hs] using hU

end IsLocalRing

namespace IsNonarchimedeanLocalField

open scoped ValuativeRel

variable (K : Type*) [Field K] [ValuativeRel K] [UniformSpace K]
  [IsUniformAddGroup K] [IsNonarchimedeanLocalField K]

/-- The actual topology on local-field integers is the maximal-ideal-adic topology. -/
theorem isAdic_integer : IsAdic 𝓂[K] :=
  IsLocalRing.isAdic_maximalIdeal_of_compact 𝒪[K]

/-- Every continuous discrete quotient of the principal units of a local field is a p-group. -/
theorem isPGroup_range_of_continuous_principalUnit_hom
    (p : ℕ) [CharP (𝒪[K] ⧸ 𝓂[K]) p]
    {H : Type*} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    (f : (Units.map (Ideal.Quotient.mk 𝓂[K] : 𝒪[K] →* 𝒪[K] ⧸ 𝓂[K])).ker →* H)
    (hf : Continuous f) : IsPGroup p f.range :=
  Ideal.isPGroup_range_of_continuous_principalUnit_hom 𝓂[K] p (isAdic_integer K) f hf

/-- Every continuous discrete image of the actual normalized-character image is a p-group. -/
theorem isPGroup_range_normalizedCharacter_image
    (p : ℕ) [Fact p.Prime] [CharP (𝒪[K] ⧸ 𝓂[K]) p]
    {G : Type*} [Group G] (ψ : G →* 𝒪[K]ˣ)
    {H : Type*} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    (f : (normalizedCharacter K p ψ).range →* H) (hf : Continuous f) :
    IsPGroup p f.range := by
  rw [isPGroup_iff_pow_pow_eq_one]
  rintro ⟨y, u, rfl⟩
  have hu : Units.map (Ideal.Quotient.mk 𝓂[K] : 𝒪[K] →* 𝒪[K] ⧸ 𝓂[K]) (u : 𝒪[K]ˣ) = 1 := by
    obtain ⟨g, hg⟩ := u.property
    rw [← hg]
    exact reduction_normalizedCharacter K p ψ g
  have ht : Filter.Tendsto (fun n : ℕ => u ^ p ^ n) Filter.atTop (nhds 1) := by
    apply tendsto_subtype_rng.mpr
    exact Ideal.tendsto_units_pow_pow_of_reduction_eq_one 𝓂[K] p (isAdic_integer K) u hu
  have he : ∀ᶠ n : ℕ in Filter.atTop, f (u ^ p ^ n) = 1 := by
    simpa only [map_one, nhds_discrete, Filter.tendsto_pure, Function.comp_def] using
      hf.continuousAt.tendsto.comp ht
  obtain ⟨n, hn⟩ := he.exists
  exact ⟨n, Subtype.ext (by simpa only [Subgroup.coe_pow, Subgroup.coe_one, map_pow] using hn)⟩

/-- The actual normalized character of a compact local Galois group has compact image. -/
theorem isCompact_range_normalizedCharacter
    (p : ℕ) [Fact p.Prime] [CharP (𝒪[K] ⧸ 𝓂[K]) p]
    {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G]
    (ψ : G →* 𝒪[K]ˣ) (hψ : Continuous ψ) :
    IsCompact (Set.range (normalizedCharacter K p ψ)) := by
  let : Finite (𝒪[K] ⧸ 𝓂[K]) := inferInstanceAs (Finite 𝓀[K])
  let : DiscreteTopology (𝒪[K] ⧸ 𝓂[K]) :=
    QuotientAddGroup.discreteTopology (IsLocalRing.isOpen_maximalIdeal 𝒪[K])
  exact Ideal.isCompact_range_teichmullerNormalizedCharacter 𝓂[K] p ψ hψ


/-- Local-field integers are totally disconnected in their actual topology. -/
theorem totallyDisconnectedSpace_integer : TotallyDisconnectedSpace 𝒪[K] := by
  let : NonarchimedeanRing 𝒪[K] := by
    change @NonarchimedeanRing 𝒪[K] _ (inferInstance : TopologicalSpace 𝒪[K])
    rw [show (inferInstance : TopologicalSpace 𝒪[K]) = Ideal.adicTopology 𝓂[K] from
      isAdic_integer K]
    exact Ideal.nonarchimedean 𝓂[K]
  infer_instance

/-- The actual integral unit group is totally disconnected. -/
theorem totallyDisconnectedSpace_integerUnits : TotallyDisconnectedSpace 𝒪[K]ˣ := by
  let := totallyDisconnectedSpace_integer K
  rw [totallyDisconnectedSpace_iff]
  exact isTotallyDisconnected_of_image Units.continuous_val.continuousOn Units.val_injective
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)

/-- The actual image of a normalized continuous character of a compact group is profinite. -/
def normalizedImageProfinite
    (p : ℕ) [Fact p.Prime] [CharP (𝒪[K] ⧸ 𝓂[K]) p]
    {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G]
    (ψ : G →* 𝒪[K]ˣ) (hψ : Continuous ψ) : ProfiniteGrp :=
  letI := totallyDisconnectedSpace_integerUnits K
  letI : CompactSpace (normalizedCharacter K p ψ).range :=
    isCompact_iff_compactSpace.mp (isCompact_range_normalizedCharacter K p ψ hψ)
  ProfiniteGrp.of (normalizedCharacter K p ψ).range

/-- Every continuous finite quotient of the actual normalized profinite image is a p-group. -/
theorem isPGroup_range_normalizedImageProfinite
    (p : ℕ) [Fact p.Prime] [CharP (𝒪[K] ⧸ 𝓂[K]) p]
    {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G]
    (ψ : G →* 𝒪[K]ˣ) (hψ : Continuous ψ)
    {H : Type*} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    (f : normalizedImageProfinite K p ψ hψ →* H) (hf : Continuous f) :
    IsPGroup p f.range :=
  isPGroup_range_normalizedCharacter_image K p ψ f hf


end IsNonarchimedeanLocalField
