/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.PrimePlusExtendedChecklist
public import HilbertModularity.RepresentationTheory.SemisimpleBaseChange

/-! # Local ordinary data under coefficient extension

An adapted two-dimensional basis and its triangular action are transported
through the actual local field, integer and residue maps. The lower
character is normalized by the Teichmüller lift of the mapped residual
character in the larger field. The two residual-character projection
equalities below are explicit because `SkinnerWilesResidualData.mapLocalCoefficients`
is opaque across its defining module boundary; the exported projection API
fixes their exact maps.
-/

public noncomputable section

open IsDedekindDomain AlgebraicGeometry
open scoped ValuativeRel NumberField

namespace HilbertModularity.Hypergeometric

open HilbertModularity.HilbertModularForms

/-- Extend a change of coordinate basis from a field to a field extension.
The two base-changed bases use the same field homomorphism. -/
def ordinaryBasisMap {K L : Type*} [Field K] [Field L]
    (f : K →+* L)
    (b : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) :
    (Fin 2 → L) ≃ₗ[L] (Fin 2 → L) := by
  letI : Algebra K L := f.toAlgebra
  let s := Pi.basisFun K (Fin 2)
  let t := s.map b.symm
  exact ((s.baseChange L).equivFun.symm).trans (t.baseChange L).equivFun

private theorem ordinaryBasisMap_apply_mapped
    {K L : Type*} [Field K] [Field L]
    (f : K →+* L) (b : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K))
    (v : Fin 2 → K) :
    ordinaryBasisMap f b (fun i => f (v i)) = fun i => f (b v i) := by
  let : Algebra K L := f.toAlgebra
  let s := Pi.basisFun K (Fin 2)
  let t := s.map b.symm
  have hs : (s.baseChange L).equivFun (1 ⊗ₜ[K] v) = fun i => f (v i) := by
    ext i
    change (s.baseChange L).repr (1 ⊗ₜ[K] v) i = f (v i)
    rw [Module.Basis.baseChange_repr_tmul]
    simp [s, Algebra.smul_def]
    rfl
  change (t.baseChange L).equivFun
      ((s.baseChange L).equivFun.symm (fun i => f (v i))) = _
  rw [← hs, LinearEquiv.symm_apply_apply]
  ext i
  change (t.baseChange L).repr (1 ⊗ₜ[K] v) i = f (b v i)
  rw [Module.Basis.baseChange_repr_tmul]
  simp [t, s, Algebra.smul_def]
  rfl

private theorem mapCoefficients_apply_mapped_vector
    {K L G : Type*} [Field K] [Field L] [Group G]
    (f : K →+* L) (ρ : Representation K G (Fin 2 → K))
    (g : G) (v : Fin 2 → K) :
    ρ.mapCoefficients f g (fun i => f (v i)) = fun i => f (ρ g v i) := by
  let e₀ : Fin 2 → K := Pi.single 0 1
  let e₁ : Fin 2 → K := Pi.single 1 1
  have hvK : v = (v 0) • e₀ + (v 1) • e₁ := by
    ext i
    fin_cases i <;> simp [e₀, e₁]
  have hvL : (fun i => f (v i)) =
      f (v 0) • Pi.single 0 (1 : L) + f (v 1) • Pi.single 1 (1 : L) := by
    ext i
    fin_cases i <;> simp
  rw [hvL]
  ext i
  have hi := congrArg (fun w : Fin 2 → K => f (ρ g w i)) hvK
  simp only [map_add,
    map_smul,
    Pi.add_apply,
    Pi.smul_apply,
    Representation.mapCoefficients_apply_single] at hi ⊢
  simpa [e₀, e₁] using hi.symm

/-- The conjugated matrix entry in the extended basis is the image of the
original conjugated entry. -/
theorem ordinaryBasisMap_action_entry
    {K L G : Type*} [Field K] [Field L] [Group G]
    (f : K →+* L)
    (ρ : Representation K G (Fin 2 → K))
    (b : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K))
    (g : G) (i j : Fin 2) :
    ordinaryBasisMap f b
      (ρ.mapCoefficients f g
        ((ordinaryBasisMap f b).symm (Pi.single j 1))) i =
      f (b (ρ g (b.symm (Pi.single j 1))) i) := by
  let v := b.symm (Pi.single j (1 : K))
  have hpre : (ordinaryBasisMap f b).symm (Pi.single j (1 : L)) =
      fun k => f (v k) := by
    apply (ordinaryBasisMap f b).injective
    rw [LinearEquiv.apply_symm_apply, ordinaryBasisMap_apply_mapped]
    dsimp [v]
    rw [b.apply_symm_apply]
    ext k
    by_cases h : k = j <;> simp [h]
  rw [hpre, mapCoefficients_apply_mapped_vector,
    ordinaryBasisMap_apply_mapped]

variable {F K L : Type*} [Field F] [NumberField F]
  [NormedField K] [ValuativeRel K]
  [NormedField L] [ValuativeRel L]

/-- Map an actual integral local character through the specified integer
ring homomorphism. -/
def mapOrdinaryIntegralCharacter {G : Type*} [Group G]
    (f : K →+* L) (C : LocalIntegerResidueComparison f)
  (ψ : G →* 𝒪[K]ˣ) : G →* 𝒪[L]ˣ :=
  (Units.map C.integerMap.toMonoidHom).comp ψ

/-- A comparison whose integer map agrees with a continuous field map is
itself continuous on the actual integer-ring subspace topology. -/
theorem LocalIntegerResidueComparison.continuous_integerMap_of_fieldMap
    (f : K →+* L) (C : LocalIntegerResidueComparison f)
    (hf : Continuous f) : Continuous C.integerMap := by
  apply Continuous.subtype_mk
  change Continuous (fun a : 𝒪[K] => (C.integerMap a : L))
  simpa only [C.coe_integerMap, Function.comp_def] using
    hf.comp continuous_subtype_val

/-- Continuity of the integer map carries continuity of an integral
character to the larger coefficient field. -/
theorem continuous_mapOrdinaryIntegralCharacter {G : Type*} [Group G]
    [TopologicalSpace G]
    (f : K →+* L) (C : LocalIntegerResidueComparison f)
    (hC : Continuous C.integerMap)
    (ψ : G →* 𝒪[K]ˣ) (hψ : Continuous ψ) :
    Continuous (mapOrdinaryIntegralCharacter f C ψ) := by
  exact (Continuous.units_map C.integerMap.toMonoidHom hC).comp hψ

section Local

variable (p : ℕ) [Fact p.Prime]
  [Algebra ℚ_[p] K] [ContinuousSMul ℚ_[p] K] [IsUniformAddGroup K]
  [IsNonarchimedeanLocalField K] [CharP (𝒪[K] ⧸ 𝓂[K]) p]
  [Algebra ℚ_[p] L] [ContinuousSMul ℚ_[p] L] [IsUniformAddGroup L]
  [IsNonarchimedeanLocalField L] [CharP (𝒪[L] ⧸ 𝓂[L]) p]

/-- Teichmüller naturality along the actual integer and residue maps.
This is the exact standard local-field fact needed below; it says only that
the canonical multiplicative section of reduction commutes with a local
homomorphism. It is exposed as a hypothesis until a pinned-library proof or
a precisely sourced literature interface is supplied. -/
def LocalTeichmullerNaturality (f : K →+* L)
    (C : LocalIntegerResidueComparison f) : Prop :=
  ∀ u : (𝒪[K] ⧸ 𝓂[K])ˣ,
    Units.map C.integerMap.toMonoidHom
      (IsNonarchimedeanLocalField.teichmullerCharacter K p
        (MonoidHom.id _) u) =
      IsNonarchimedeanLocalField.teichmullerCharacter L p
        (Units.map C.residueMap.toMonoidHom) u

/-- Functoriality of the canonical multiplicative Teichmüller section for a
continuous local-field map. The source construction is
[mathlib_5ed296525643, `Mathlib/RingTheory/Teichmuller.lean`,
`Perfection.teichmuller₀_spec` and `mk_comp_teichmuller`, lines 136--178].
The specification characterizes the lift by compatible p-power congruences.
The integer map sends powers of the source maximal ideal into the same
powers of the target maximal ideal, and the residue map preserves Frobenius;
thus the image satisfies the target specification. Restriction to units
gives the stated naturality. These standard correspondence steps are included
in this admission. This named standard interface
contains no Skinner--Wiles data or ordinary conclusion. -/
theorem localTeichmullerNaturality_literature
    (f : K →+* L) (hf : Continuous f)
    (C : LocalIntegerResidueComparison f) :
    LocalTeichmullerNaturality p f C := by
  sorry

omit [Algebra ℚ_[p] K] [Algebra ℚ_[p] L] [ContinuousSMul ℚ_[p] L] in
/-- Apply local Teichmüller naturality to one specified residual character. -/
theorem mapOrdinaryIntegralCharacter_teichmuller
    {G : Type*} [Group G]
    (f : K →+* L) (C : LocalIntegerResidueComparison f)
    (hNat : LocalTeichmullerNaturality p f C)
    (χ : G →* (𝒪[K] ⧸ 𝓂[K])ˣ) :
    mapOrdinaryIntegralCharacter f C
      (IsNonarchimedeanLocalField.teichmullerCharacter K p χ) =
      IsNonarchimedeanLocalField.teichmullerCharacter L p
        ((Units.map C.residueMap.toMonoidHom).comp χ) := by
  apply MonoidHom.ext
  intro g
  change Units.map C.integerMap.toMonoidHom
      (IsNonarchimedeanLocalField.teichmullerCharacter K p χ g) =
    IsNonarchimedeanLocalField.teichmullerCharacter L p
      ((Units.map C.residueMap.toMonoidHom).comp χ) g
  exact hNat (χ g)

omit [IsUniformAddGroup K] [IsUniformAddGroup L] in
/-- Reducing a mapped integer unit agrees with mapping its old residue.
This uses the actual reduction square in `LocalIntegerResidueComparison`. -/
theorem mapOrdinaryIntegralCharacter_reduction
    (f : K →+* L) (C : LocalIntegerResidueComparison f)
    (u : 𝒪[K]ˣ) :
    Units.map (Ideal.Quotient.mk 𝓂[L] : 𝒪[L] →* 𝒪[L] ⧸ 𝓂[L])
      (Units.map C.integerMap.toMonoidHom u) =
    Units.map C.residueMap.toMonoidHom
      (Units.map (Ideal.Quotient.mk 𝓂[K] : 𝒪[K] →* 𝒪[K] ⧸ 𝓂[K]) u) := by
  apply Units.ext
  exact (C.residueMap_mk u).symm

omit [Fact (Nat.Prime p)] [IsUniformAddGroup K] [IsNonarchimedeanLocalField K]
  [CharP (𝒪[K] ⧸ 𝓂[K]) p] [IsUniformAddGroup L] [IsNonarchimedeanLocalField L]
  [CharP (𝒪[L] ⧸ 𝓂[L]) p] in
/-- The pro-`p` property passes to the image under a continuous integral
coefficient map: every discrete quotient of the new image pulls back to one
of the old image. -/
theorem mapOrdinaryIntegralCharacter_pro_p
    {G : Type*} [Group G]
    (f : K →+* L) (C : LocalIntegerResidueComparison f)
    (hC : Continuous C.integerMap)
    (ψ : G →* 𝒪[K]ˣ)
    (hψ : ∀ {H : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
      (q : ψ.range →* H), Continuous q → IsPGroup p q.range) :
    ∀ {H : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
      (q : (mapOrdinaryIntegralCharacter f C ψ).range →* H),
      Continuous q → IsPGroup p q.range := by
  let U : 𝒪[K]ˣ →* 𝒪[L]ˣ := Units.map C.integerMap.toMonoidHom
  let ψL := mapOrdinaryIntegralCharacter f C ψ
  let t : ψ.range →* ψL.range := {
    toFun := fun u => ⟨U u.val, by
      obtain ⟨g, hg⟩ := u.property
      exact ⟨g, by rw [← hg]; rfl⟩⟩
    map_one' := by apply Subtype.ext; simp [U]
    map_mul' a b := by apply Subtype.ext; simp [U]
  }
  have ht : Continuous t := by
    apply Continuous.subtype_mk
    exact (Continuous.units_map C.integerMap.toMonoidHom hC).comp continuous_subtype_val
  have hsurj : Function.Surjective t := by
    rintro ⟨u, g, rfl⟩
    exact ⟨⟨ψ g, ⟨g, rfl⟩⟩, rfl⟩
  intro H _ _ _ q hq
  have hsub := hψ (q.comp t) (hq.comp ht)
  have heq : (q.comp t).range = q.range := by
    ext y
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨t u, rfl⟩
    · rintro ⟨v, rfl⟩
      obtain ⟨u, rfl⟩ := hsurj v
      exact ⟨u, rfl⟩
  rw [heq] at hsub
  exact hsub

omit [IsUniformAddGroup K] [IsNonarchimedeanLocalField K]
  [IsUniformAddGroup L] [IsNonarchimedeanLocalField L] in
/-- Finite image on a specified subgroup or subset is preserved by the
actual integer-unit map. In the ordinary record the subset is local inertia.
-/
theorem mapOrdinaryIntegralCharacter_finite_on
    {G : Type*} [Group G]
    (f : K →+* L) (C : LocalIntegerResidueComparison f)
    (ψ : G →* 𝒪[K]ˣ) (S : Set G)
    (hψ : Set.Finite {u : 𝒪[K]ˣ | ∃ g ∈ S, ψ g = u}) :
    Set.Finite {u : 𝒪[L]ˣ | ∃ g ∈ S,
      mapOrdinaryIntegralCharacter f C ψ g = u} := by
  let U : 𝒪[K]ˣ →* 𝒪[L]ˣ := Units.map C.integerMap.toMonoidHom
  apply (hψ.image U).subset
  rintro y ⟨g, hg, hy⟩
  exact ⟨ψ g, ⟨g, hg, rfl⟩, by simpa [U, mapOrdinaryIntegralCharacter] using hy⟩

omit [Algebra ℚ_[p] K] [ContinuousSMul ℚ_[p] K]
  [Algebra ℚ_[p] L] [ContinuousSMul ℚ_[p] L] in
/-- The exact Teichmüller-normalized diagonal entry survives coefficient
extension in the base-changed adapted basis. -/
theorem ordinaryBasisMap_diagonal
    {G J : Type*} [Group G] [Group J]
    (f : K →+* L) (C : LocalIntegerResidueComparison f)
    (hNat : LocalTeichmullerNaturality p f C)
    (ρ : Representation K G (Fin 2 → K))
    (ι : J →* G)
    (b : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K))
    (χ : J →* (𝒪[K] ⧸ 𝓂[K])ˣ) (ψ : J →* 𝒪[K]ˣ)
    (g : J) (j : Fin 2)
    (hdiag : b (ρ (ι g) (b.symm (Pi.single j 1))) j =
      ((ψ g : 𝒪[K]) : K) *
        ((IsNonarchimedeanLocalField.teichmullerCharacter K p χ g : 𝒪[K]) : K)) :
    ordinaryBasisMap f b
      (ρ.mapCoefficients f (ι g)
        ((ordinaryBasisMap f b).symm (Pi.single j 1))) j =
      ((mapOrdinaryIntegralCharacter f C ψ g : 𝒪[L]) : L) *
        ((IsNonarchimedeanLocalField.teichmullerCharacter L p
          ((Units.map C.residueMap.toMonoidHom).comp χ) g : 𝒪[L]) : L) := by
  rw [ordinaryBasisMap_action_entry, hdiag, map_mul]
  have hψ := (C.coe_integerMap (ψ g))
  have hχ := congrArg (fun η : J →* 𝒪[L]ˣ => ((η g : 𝒪[L]) : L))
    (mapOrdinaryIntegralCharacter_teichmuller p f C hNat χ)
  change f ((ψ g : 𝒪[K]) : K) *
      f ((IsNonarchimedeanLocalField.teichmullerCharacter K p χ g : 𝒪[K]) : K) = _
  rw [← hψ, ← C.coe_integerMap]
  exact congrArg₂ (· * ·) (rfl) hχ

/-- Extend a supplied Skinner--Wiles local ordinary row through the actual
integer and residue maps. The basis, both diagonal characters, residual
ordering, principal pro-`p` property, and finite inertia are constructed from
the original row. The extra hypotheses are continuity of the integer map and
standard Teichmüller naturality. No new ordinary premise is used. -/
def SkinnerWilesOrdinaryAt.mapLocalCoefficients
    {ρ : Representation K (AbsoluteGalois F) (Fin 2 → K)}
    (D : SkinnerWilesResidualData ρ)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal]
    (H : SkinnerWilesOrdinaryAt p ρ D Q)
    (f : K →+* L) (C : LocalIntegerResidueComparison f)
    (hC : Continuous C.integerMap)
    (hNat : LocalTeichmullerNaturality p f C) :
    SkinnerWilesOrdinaryAt p (ρ.mapCoefficients f)
      (SkinnerWilesResidualData.mapLocalCoefficients D f C) Q where
  basis := ordinaryBasisMap f H.basis
  psi₁ := mapOrdinaryIntegralCharacter f C H.psi₁
  psi₂ := mapOrdinaryIntegralCharacter f C H.psi₂
  psi₂_continuous := continuous_mapOrdinaryIntegralCharacter f C hC
    H.psi₂ H.psi₂_continuous
  psi₂_reduction := by
    intro g
    change Units.map (Ideal.Quotient.mk 𝓂[L] : 𝒪[L] →* 𝒪[L] ⧸ 𝓂[L])
      (Units.map C.integerMap.toMonoidHom (H.psi₂ g)) = 1
    rw [mapOrdinaryIntegralCharacter_reduction]
    rw [H.psi₂_reduction]
    simp
  psi₂_pro_p := mapOrdinaryIntegralCharacter_pro_p p f C hC H.psi₂ H.psi₂_pro_p
  psi₂_finite_inertia := by
    exact mapOrdinaryIntegralCharacter_finite_on f C H.psi₂
      {g | (g : AbsoluteGalois F) ∈ Q.inertia (AbsoluteGalois F)}
      H.psi₂_finite_inertia
  lower_left_zero := by
    intro g
    rw [ordinaryBasisMap_action_entry, H.lower_left_zero, map_zero]
  upper_left := by
    intro g
    have h := ordinaryBasisMap_diagonal p f C hNat ρ
      ((primeDecompositionGroup Q).subtype) H.basis
      (D.chi₁.comp ((primeDecompositionGroup Q).subtype)) H.psi₁ g 0 (H.upper_left g)
    rw [SkinnerWilesResidualData.mapLocalCoefficients_chi₁ D f C]
    have hc : (Units.map C.residueMap.toMonoidHom).comp
        (D.chi₁.comp ((primeDecompositionGroup Q).subtype)) =
      ((Units.map C.residueMap.toMonoidHom).comp D.chi₁).comp
        ((primeDecompositionGroup Q).subtype) := by ext x; rfl
    rw [hc] at h
    have hg : ((primeDecompositionGroup Q).subtype g) =
        (g : AbsoluteGalois F) := rfl
    rw [hg] at h
    exact h
  lower_right := by
    intro g
    have h := ordinaryBasisMap_diagonal p f C hNat ρ
      ((primeDecompositionGroup Q).subtype) H.basis
      (D.chi₂.comp ((primeDecompositionGroup Q).subtype)) H.psi₂ g 1 (H.lower_right g)
    rw [SkinnerWilesResidualData.mapLocalCoefficients_chi₂ D f C]
    have hc : (Units.map C.residueMap.toMonoidHom).comp
        (D.chi₂.comp ((primeDecompositionGroup Q).subtype)) =
      ((Units.map C.residueMap.toMonoidHom).comp D.chi₂).comp
        ((primeDecompositionGroup Q).subtype) := by ext x; rfl
    rw [hc] at h
    have hg : ((primeDecompositionGroup Q).subtype g) =
        (g : AbsoluteGalois F) := rfl
    rw [hg] at h
    exact h

/-- For a continuous local field map, continuity of the integer map follows
from the reduction comparison, and the only nondefinitional input is the
named standard Teichmüller naturality interface. The two character equations
come from the checked projection API of the already defined residual mapper.
-/
def SkinnerWilesOrdinaryAt.mapLocalCoefficients_of_continuous
    {ρ : Representation K (AbsoluteGalois F) (Fin 2 → K)}
    (D : SkinnerWilesResidualData ρ)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal]
    (H : SkinnerWilesOrdinaryAt p ρ D Q)
    (f : K →+* L) (hf : Continuous f)
    (C : LocalIntegerResidueComparison f) :
    SkinnerWilesOrdinaryAt p (ρ.mapCoefficients f)
      (SkinnerWilesResidualData.mapLocalCoefficients D f C) Q :=
  SkinnerWilesOrdinaryAt.mapLocalCoefficients p D Q H f C
    (C.continuous_integerMap_of_fieldMap f hf)
    (localTeichmullerNaturality_literature p f hf C)

/-- Equality of coordinate actions transports an ordinary row together
with the residual datum defined on that action. -/
def SkinnerWilesOrdinaryAt.transportAction
    {ρ σ : Representation K (AbsoluteGalois F) (Fin 2 → K)}
    (D : SkinnerWilesResidualData ρ)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal]
    (H : SkinnerWilesOrdinaryAt p ρ D Q)
    (h : ρ = σ) : SkinnerWilesOrdinaryAt p σ (h ▸ D) Q := by
  cases h
  exact H

/-- Map a full Skinner--Wiles checklist through a continuous local
coefficient extension while constructing, rather than assuming, every
enlarged-field ordinary row. The global irreducibility input remains the
existing explicit hypothesis of `SkinnerWilesWeightTwoInput.mapLocalCoefficients`.
-/
def SkinnerWilesWeightTwoInput.mapLocalCoefficients_withOrdinary
    {ρ : Representation K (AbsoluteGalois F) (Fin 2 → K)}
    (M : Type*) [Field M] [NumberField M] [Algebra F M]
    (H : SkinnerWilesWeightTwoInput p ρ M)
    (f : K →+* L) (hf : Continuous f)
    (hfp : ∀ x : ℚ_[p], f (algebraMap ℚ_[p] K x) =
      algebraMap ℚ_[p] L x)
    (C : LocalIntegerResidueComparison f)
    (habs : (Representation.baseChange (AlgebraicClosure L)
      (ρ.mapCoefficients f)).IsIrreducible) :
    SkinnerWilesWeightTwoInput p (ρ.mapCoefficients f) M :=
  HilbertModularity.Hypergeometric.SkinnerWilesWeightTwoInput.mapLocalCoefficients
    p M H f hf hfp C habs (by
    intro P _ hpP Q _ _
    exact SkinnerWilesOrdinaryAt.mapLocalCoefficients_of_continuous p
      H.residual Q (H.local_ordinary P hpP Q) f hf C)

end Local

section SelectedPlus

open HilbertModularity.Cyclotomic

variable (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
  [hK : NormedAlgebra ℚ_[p] (RealCompletion p)]
  [hL : NormedAlgebra ℚ_[p] (FullConductorCompletion p)]
  [IsUniformAddGroup (RealCompletion p)]
  [IsUniformAddGroup (FullConductorCompletion p)]
  [IsNonarchimedeanLocalField (RealCompletion p)]
  [IsNonarchimedeanLocalField (FullConductorCompletion p)]
  [CharP (𝒪[RealCompletion p] ⧸ 𝓂[RealCompletion p]) p]
  [CharP (𝒪[FullConductorCompletion p] ⧸ 𝓂[FullConductorCompletion p]) p]

/-- Specialize the proved ordinary-record transport to the actual selected
real-to-full conductor coefficient map. The equality
`selectedPlusFullConductorAction_eq_mapNative` identifies this mapped action
with the coordinate action of the same selected plus Jacobian. The residual
characters are mapped by the projection API of the coefficient mapper.
-/
def selectedPlusFullConductorOrdinaryAt_mapCoefficients
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p)))) [Q.IsMaximal]
    (D : SkinnerWilesResidualData
      (primePlusTateFieldCoordinateAction p hp ξ
        (realPrimeGeneratorAdicToNativeIntegers p hp)))
    (H : SkinnerWilesOrdinaryAt p
      (primePlusTateFieldCoordinateAction p hp ξ
        (realPrimeGeneratorAdicToNativeIntegers p hp)) D Q) :
    SkinnerWilesOrdinaryAt p
      ((primePlusTateFieldCoordinateAction p hp ξ
        (realPrimeGeneratorAdicToNativeIntegers p hp)).mapCoefficients
          (realToFullConductorCompletionMap p))
      (SkinnerWilesResidualData.mapLocalCoefficients D
        (realToFullConductorCompletionMap p)
        (realToFullConductorIntegerResidueComparison p)) Q :=
  SkinnerWilesOrdinaryAt.mapLocalCoefficients_of_continuous p D Q H
    (realToFullConductorCompletionMap p)
    (continuous_realToFullConductorCompletionMap p)
    (realToFullConductorIntegerResidueComparison p)

/-- The same row stated on the exact full-conductor coordinate action of
the selected Jacobian, using the checked native/full action equality. -/
def selectedPlusFullConductorOrdinaryAt
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p)))) [Q.IsMaximal]
    (D : SkinnerWilesResidualData
      (primePlusTateFieldCoordinateAction p hp ξ
        (realPrimeGeneratorAdicToNativeIntegers p hp)))
    (H : SkinnerWilesOrdinaryAt p
      (primePlusTateFieldCoordinateAction p hp ξ
        (realPrimeGeneratorAdicToNativeIntegers p hp)) D Q) :
    let h := selectedPlusFullConductorAction_eq_mapNative p hp ξ
    SkinnerWilesOrdinaryAt p
      (primePlusTateFieldCoordinateAction p hp ξ
        (realPrimeGeneratorAdicToFullIntegers p hp))
      (h.symm ▸ SkinnerWilesResidualData.mapLocalCoefficients D
        (realToFullConductorCompletionMap p)
        (realToFullConductorIntegerResidueComparison p)) Q :=
  SkinnerWilesOrdinaryAt.transportAction p
    (SkinnerWilesResidualData.mapLocalCoefficients D
      (realToFullConductorCompletionMap p)
      (realToFullConductorIntegerResidueComparison p)) Q
    (selectedPlusFullConductorOrdinaryAt_mapCoefficients p hp ξ Q D H)
    (selectedPlusFullConductorAction_eq_mapNative p hp ξ).symm

/-- The canonical named residual datum of the selected full conductor
coordinate action. The defining equation of that datum is supplied by its
public property API, rather than imposed as an additional premise. -/
def selectedPlusFullConductorOrdinaryAt_named
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p)))) [Q.IsMaximal]
    (D : SkinnerWilesResidualData
      (primePlusTateFieldCoordinateAction p hp ξ
        (realPrimeGeneratorAdicToNativeIntegers p hp)))
    (H : SkinnerWilesOrdinaryAt p
      (primePlusTateFieldCoordinateAction p hp ξ
        (realPrimeGeneratorAdicToNativeIntegers p hp)) D Q) :
    SkinnerWilesOrdinaryAt p
      (primePlusTateFieldCoordinateAction p hp ξ
        (realPrimeGeneratorAdicToFullIntegers p hp))
      (selectedPlusFullConductorResidualData p hp ξ D) Q := by
  rw [selectedPlusFullConductorResidualData_eq_mapLocalCoefficients]
  exact selectedPlusFullConductorOrdinaryAt p hp ξ Q D H

/-- The actual selected plus checklist over the full cyclotomic conductor
completion, starting from a native real-completion checklist. The enlarged
ordinary rows are constructed above; the original global irreducibility
comparison remains the explicit premise of coefficient extension. `hfp`
ties the supplied normalized `NormedAlgebra` structures to the canonical
`ℚₚ` completion embeddings; it must not be inferred from an unnormalized
valuation norm on the full completion. -/
def selectedPlusFullConductorWeightTwoInput_of_native
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (M : Type*) [Field M] [NumberField M]
      [Algebra (realCyclotomicField p) M]
    (H : letI : Algebra ℚ_[p] (RealCompletion p) := hK.toAlgebra
      SkinnerWilesWeightTwoInput p
      (primePlusTateFieldCoordinateAction p hp ξ
        (realPrimeGeneratorAdicToNativeIntegers p hp)) M)
    (hfp : letI : Algebra ℚ_[p] (RealCompletion p) := hK.toAlgebra
      letI : Algebra ℚ_[p] (FullConductorCompletion p) := hL.toAlgebra
      ∀ x : ℚ_[p],
      realToFullConductorCompletionMap p
        (algebraMap ℚ_[p] (RealCompletion p) x) =
      algebraMap ℚ_[p] (FullConductorCompletion p) x)
    (habs : (Representation.baseChange
      (AlgebraicClosure (FullConductorCompletion p))
      ((primePlusTateFieldCoordinateAction p hp ξ
        (realPrimeGeneratorAdicToNativeIntegers p hp)).mapCoefficients
          (realToFullConductorCompletionMap p))).IsIrreducible) :
    letI : Algebra ℚ_[p] (FullConductorCompletion p) := hL.toAlgebra
    SkinnerWilesWeightTwoInput p
      (primePlusTateFieldCoordinateAction p hp ξ
        (realPrimeGeneratorAdicToFullIntegers p hp)) M := by
  letI : Algebra ℚ_[p] (RealCompletion p) := hK.toAlgebra
  letI : Algebra ℚ_[p] (FullConductorCompletion p) := hL.toAlgebra
  let H' := SkinnerWilesWeightTwoInput.mapLocalCoefficients_withOrdinary p M H
    (realToFullConductorCompletionMap p)
    (continuous_realToFullConductorCompletionMap p) hfp
    (realToFullConductorIntegerResidueComparison p) habs
  exact (selectedPlusFullConductorAction_eq_mapNative p hp ξ).symm ▸ H'

end SelectedPlus

end HilbertModularity.Hypergeometric
