/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.HilbertModularForms.SkinnerWilesInput
import HilbertModularity.NumberTheory.HilbertModularForms.GaloisTwist
public import HilbertModularity.RepresentationTheory.CharacterTwist

/-! # Finite character twists of the Skinner--Wiles input

An integral finite character changes both residual characters by the same
factor and preserves their ratio. Its Teichmüller-normalized local factor is a
principal-unit character. These are the generic steps needed before applying
[SkinnerWiles, §4.5, Theorem A] to a finite twist of a covariant representation.
-/

public noncomputable section

open NumberField IsDedekindDomain
open scoped ValuativeRel

namespace Representation

variable {K A G V : Type*} [Field K] [Field A] [Algebra K A]
  [Group G] [AddCommGroup V] [Module K V]

/-- Scalar extension commutes with multiplication of a representation by a
character, with the character values mapped to the larger coefficient field. -/
theorem baseChange_characterTwist (ρ : Representation K G V) (χ : G →* Kˣ) :
    (ρ.characterTwist χ).baseChange A =
      (ρ.baseChange A).characterTwist
        ((Units.map (algebraMap K A : K →+* A).toMonoidHom).comp χ) := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul a v =>
    change a ⊗ₜ[K] ((χ g : K) • ρ g v) =
      ((algebraMap K A (χ g : K)) : A) • (a ⊗ₜ[K] ρ g v)
    rw [Representation.baseChange_balance]
    rw [TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- A character twist has the same invariant subspaces and hence preserves
irreducibility. -/
theorem isIrreducible_characterTwist
    (ρ : Representation K G V) (χ : G →* Kˣ) [ρ.IsIrreducible] :
    (ρ.characterTwist χ).IsIrreducible := by
  let e := ρ.characterTwistSubrepresentationEquiv χ
  have hne : (⊥ : Subrepresentation (ρ.characterTwist χ)) ≠ ⊤ := by
    intro h
    have h' : (⊥ : Subrepresentation ρ) = ⊤ := by
      apply e.injective
      simpa only [map_bot, map_top] using h
    exact bot_ne_top h'
  let : Nontrivial (Subrepresentation (ρ.characterTwist χ)) :=
    ⟨⟨⊥, ⊤, hne⟩⟩
  apply IsSimpleOrder.of_forall_eq_top
  intro S hS
  obtain ⟨T, rfl⟩ := e.surjective S
  rcases eq_bot_or_eq_top T with h | h
  · exact (hS (by simp [h])).elim
  · simp [h]

end Representation

namespace HilbertModularity.HilbertModularForms

variable {F : Type*} [Field F] [NumberField F]
variable (p : ℕ) [Fact p.Prime]
variable {E : Type*} [NormedField E] [ValuativeRel E]
  [NormedAlgebra ℚ_[p] E] [UniformSpace E]
  [IsUniformAddGroup E] [IsNonarchimedeanLocalField E]
  [CharP (𝒪[E] ⧸ 𝓂[E]) p]

/-- Extend an integral unit character to the coefficient field. -/
def integralCharacterToField
    (u : AbsoluteGalois F →* 𝒪[E]ˣ) : AbsoluteGalois F →* Eˣ :=
  (Units.map (algebraMap 𝒪[E] E : 𝒪[E] →* E)).comp u

omit [NumberField F] [UniformSpace E] [IsUniformAddGroup E]
    [IsNonarchimedeanLocalField E] in
/-- The field value of an integral character is the image of its unit value. -/
theorem integralCharacterToField_apply
    (u : AbsoluteGalois F →* 𝒪[E]ˣ) (g : AbsoluteGalois F) :
    integralCharacterToField u g =
      (Units.map (algebraMap 𝒪[E] E : 𝒪[E] →* E)) (u g) := (rfl)

omit [NumberField F] [IsUniformAddGroup E]
    [IsNonarchimedeanLocalField E] in
/-- A continuous integral character remains continuous over the coefficient
field. -/
theorem continuous_integralCharacterToField
    (u : AbsoluteGalois F →* 𝒪[E]ˣ) (hu : Continuous u) :
    Continuous (integralCharacterToField u) :=
  (Continuous.units_map _ continuous_subtype_val).comp hu

omit [NumberField F] [UniformSpace E] [IsUniformAddGroup E]
    [IsNonarchimedeanLocalField E] in
/-- Passing from integral units to field units preserves finite image. -/
theorem finite_range_integralCharacterToField
    (u : AbsoluteGalois F →* 𝒪[E]ˣ) (hu : (Set.range u).Finite) :
    (Set.range (integralCharacterToField u)).Finite := by
  apply (hu.image (Units.map (algebraMap 𝒪[E] E : 𝒪[E] →* E))).subset
  rintro a ⟨g, rfl⟩
  exact ⟨u g, ⟨g, rfl⟩, rfl⟩

/-- The finite determinant factor after a rank-two scalar twist. -/
def determinantCharacterTwist
    (ψ : AbsoluteGalois F →* Eˣ)
    (u : AbsoluteGalois F →* 𝒪[E]ˣ) :
    AbsoluteGalois F →* Eˣ where
  toFun g := ψ g * integralCharacterToField u g ^ 2
  map_one' := by simp
  map_mul' g h := by simp only [map_mul, mul_pow]; ac_rfl

omit [NumberField F] [UniformSpace E] [IsUniformAddGroup E]
    [IsNonarchimedeanLocalField E] in
/-- The new finite determinant factor is still finite order. -/
theorem finite_range_determinantCharacterTwist
    (ψ : AbsoluteGalois F →* Eˣ)
    (u : AbsoluteGalois F →* 𝒪[E]ˣ)
    (hψ : (Set.range ψ).Finite) (hu : (Set.range u).Finite) :
    (Set.range (determinantCharacterTwist ψ u)).Finite := by
  let T : Set Eˣ := Set.range (integralCharacterToField u)
  have hT : T.Finite := finite_range_integralCharacterToField u hu
  have hprod : ((Set.range ψ) ×ˢ T).Finite := hψ.prod hT
  apply (hprod.image (fun z : Eˣ × Eˣ => z.1 * z.2 ^ 2)).subset
  rintro a ⟨g, rfl⟩
  exact ⟨(ψ g, integralCharacterToField u g),
    ⟨⟨g, rfl⟩, ⟨g, rfl⟩⟩, rfl⟩

/-- The actual scalar twist of an integral rank-two Galois action. -/
def integralRepresentationTwist
    (ρ : Representation (𝒪[E]) (AbsoluteGalois F) (Fin 2 → 𝒪[E]))
    (u : AbsoluteGalois F →* 𝒪[E]ˣ) :
    Representation (𝒪[E]) (AbsoluteGalois F) (Fin 2 → 𝒪[E]) where
  toFun g := (u g : 𝒪[E]) • ρ g
  map_one' := by simp
  map_mul' g h := by simp [smul_smul, mul_comm]

omit [NumberField F] [UniformSpace E] [IsUniformAddGroup E]
    [IsNonarchimedeanLocalField E] in
@[simp]
theorem integralRepresentationTwist_apply
    (ρ : Representation (𝒪[E]) (AbsoluteGalois F) (Fin 2 → 𝒪[E]))
    (u : AbsoluteGalois F →* 𝒪[E]ˣ) (g : AbsoluteGalois F)
    (v : Fin 2 → 𝒪[E]) :
    integralRepresentationTwist ρ u g v = (u g : 𝒪[E]) • ρ g v := by
  rfl

/-- Reduce an integral character to the residue-field units. -/
def residualCharacter
    (u : AbsoluteGalois F →* 𝒪[E]ˣ) :
    AbsoluteGalois F →* (𝒪[E] ⧸ 𝓂[E])ˣ :=
  (Units.map (Ideal.Quotient.mk 𝓂[E] : 𝒪[E] →* 𝒪[E] ⧸ 𝓂[E])).comp u

/-- Pointwise multiplication of two residual characters. -/
def residualCharacterProduct {G : Type*} [Group G]
    (χ η : G →* (𝒪[E] ⧸ 𝓂[E])ˣ) : G →* (𝒪[E] ⧸ 𝓂[E])ˣ where
  toFun g := χ g * η g
  map_one' := by simp
  map_mul' g h := by simp only [map_mul]; ac_rfl

@[simp]
theorem residualCharacterProduct_apply {G : Type*} [Group G]
    (χ η : G →* (𝒪[E] ⧸ 𝓂[E])ˣ) (g : G) :
    residualCharacterProduct χ η g = χ g * η g := (rfl)

/-- The two residual characters acquire the same scalar factor. -/
def SkinnerWilesResidualData.characterTwist
    {ρ : Representation E (AbsoluteGalois F) (Fin 2 → E)}
    (D : SkinnerWilesResidualData ρ)
    (u : AbsoluteGalois F →* 𝒪[E]ˣ) :
    SkinnerWilesResidualData
      (ρ.characterTwist (integralCharacterToField u)) where
  integralAction := integralRepresentationTwist D.integralAction u
  integral_spec := by
    intro g i j
    rw [integralRepresentationTwist_apply, Representation.characterTwist_apply]
    simp only [Pi.smul_apply, smul_eq_mul, Subring.coe_mul]
    rw [D.integral_spec]
    rfl
  chi₁ := residualCharacterProduct D.chi₁ (residualCharacter u)
  chi₂ := residualCharacterProduct D.chi₂ (residualCharacter u)
  residual_trace := by
    intro g
    change Ideal.Quotient.mk 𝓂[E]
        (LinearMap.trace (𝒪[E]) (Fin 2 → 𝒪[E])
          ((u g : 𝒪[E]) • D.integralAction g)) =
      ((D.chi₁ g * residualCharacter u g : (𝒪[E] ⧸ 𝓂[E])ˣ) :
        𝒪[E] ⧸ 𝓂[E]) +
      ((D.chi₂ g * residualCharacter u g : (𝒪[E] ⧸ 𝓂[E])ˣ) :
        𝒪[E] ⧸ 𝓂[E])
    simp only [map_smul, smul_eq_mul, map_mul, Units.val_mul]
    rw [D.residual_trace]
    simp [residualCharacter, add_mul, mul_comm]
  residual_det := by
    intro g
    change Ideal.Quotient.mk 𝓂[E]
        (LinearMap.det ((u g : 𝒪[E]) • D.integralAction g)) =
      ((D.chi₁ g * residualCharacter u g : (𝒪[E] ⧸ 𝓂[E])ˣ) :
        𝒪[E] ⧸ 𝓂[E]) *
      ((D.chi₂ g * residualCharacter u g : (𝒪[E] ⧸ 𝓂[E])ˣ) :
        𝒪[E] ⧸ 𝓂[E])
    simp only [LinearMap.det_smul, map_mul, map_pow, Units.val_mul]
    rw [D.residual_det]
    simp [residualCharacter, pow_two, mul_comm]
    ring

omit [NumberField F] in
/-- A scalar twist multiplies both residual constituents by the same character,
so their quotient is unchanged. -/
@[simp]
theorem residualRatio_characterTwist
    {ρ : Representation E (AbsoluteGalois F) (Fin 2 → E)}
    (D : SkinnerWilesResidualData ρ)
    (u : AbsoluteGalois F →* 𝒪[E]ˣ) :
    residualRatio (D.characterTwist u) = residualRatio D := by
  apply MonoidHom.ext
  intro g
  simp only [residualRatio_apply]
  change (D.chi₁ g * residualCharacter u g) *
      (D.chi₂ g * residualCharacter u g)⁻¹ = D.chi₁ g * (D.chi₂ g)⁻¹
  group

/-- The extension cut out by the residual ratio is unchanged by twisting. -/
def SkinnerWilesRatioField.characterTwist
    {ρ : Representation E (AbsoluteGalois F) (Fin 2 → E)}
    {D : SkinnerWilesResidualData ρ}
    {L : Type*} [Field L] [NumberField L] [Algebra F L]
    (H : SkinnerWilesRatioField D L)
    (u : AbsoluteGalois F →* 𝒪[E]ˣ) :
    SkinnerWilesRatioField (D.characterTwist u) L where
  embedding := H.embedding
  galois_over_rat := H.galois_over_rat
  abelian_over_rat := H.abelian_over_rat
  cuts_out_ratio := by
    intro g
    rw [residualRatio_characterTwist]
    exact H.cuts_out_ratio g

omit [Fact p.Prime] [NormedAlgebra ℚ_[p] E] in
/-- Every continuous discrete quotient of the image of a character taking
values in principal units is a `p`-group. -/
theorem isPGroup_range_principalCharacter
    {G : Type*} [Group G]
    (ψ : G →* 𝒪[E]ˣ)
    (hψ : ∀ g,
      Units.map (Ideal.Quotient.mk 𝓂[E] : 𝒪[E] →* 𝒪[E] ⧸ 𝓂[E]) (ψ g) = 1)
    {H : Type*} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    (f : ψ.range →* H) (hf : Continuous f) :
    IsPGroup p f.range := by
  rw [isPGroup_iff_pow_pow_eq_one]
  rintro ⟨y, v, rfl⟩
  obtain ⟨g, hg⟩ := v.property
  have hv : Units.map (Ideal.Quotient.mk 𝓂[E] : 𝒪[E] →* 𝒪[E] ⧸ 𝓂[E])
      (v : 𝒪[E]ˣ) = 1 := by
    rw [← hg]
    exact hψ g
  have ht : Filter.Tendsto (fun n : ℕ => v ^ p ^ n) Filter.atTop (nhds 1) := by
    apply tendsto_subtype_rng.mpr
    exact Ideal.tendsto_units_pow_pow_of_reduction_eq_one 𝓂[E] p
      (IsNonarchimedeanLocalField.isAdic_integer E) v hv
  have he : ∀ᶠ n : ℕ in Filter.atTop, f (v ^ p ^ n) = 1 := by
    simpa only [map_one, nhds_discrete, Filter.tendsto_pure, Function.comp_def] using
      hf.continuousAt.tendsto.comp ht
  obtain ⟨n, hn⟩ := he.exists
  exact ⟨n, Subtype.ext (by simpa only [Subgroup.coe_pow, Subgroup.coe_one, map_pow] using hn)⟩

/-- Restrict the integral twisting character to a prime decomposition group. -/
def localIntegralCharacter
    (u : AbsoluteGalois F →* 𝒪[E]ˣ)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) :
    primeDecompositionGroup Q →* 𝒪[E]ˣ :=
  u.comp (primeDecompositionGroup Q).subtype

/-- The principal-unit factor of a local finite character. -/
def localNormalizedTwistCharacter
    (u : AbsoluteGalois F →* 𝒪[E]ˣ)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) :
    primeDecompositionGroup Q →* 𝒪[E]ˣ :=
  IsNonarchimedeanLocalField.normalizedCharacter E p (localIntegralCharacter u Q)

omit [NumberField F] [NormedAlgebra ℚ_[p] E] in
@[simp]
theorem localNormalizedTwistCharacter_reduction
    (u : AbsoluteGalois F →* 𝒪[E]ˣ)
    (Q : Ideal (𝓞 (AlgebraicClosure F)))
    (g : primeDecompositionGroup Q) :
    Units.map (Ideal.Quotient.mk 𝓂[E] : 𝒪[E] →* 𝒪[E] ⧸ 𝓂[E])
      (localNormalizedTwistCharacter p u Q g) = 1 :=
  IsNonarchimedeanLocalField.reduction_normalizedCharacter E p
    (localIntegralCharacter u Q) g

omit [NumberField F] [NormedAlgebra ℚ_[p] E] in
/-- The normalized factor times the Teichmüller lift recovers the original
local character. -/
theorem localNormalizedTwistCharacter_mul_teichmuller
    (u : AbsoluteGalois F →* 𝒪[E]ˣ)
    (Q : Ideal (𝓞 (AlgebraicClosure F)))
    (g : primeDecompositionGroup Q) :
    localNormalizedTwistCharacter p u Q g *
      IsNonarchimedeanLocalField.teichmullerCharacter E p
        ((residualCharacter u).comp (primeDecompositionGroup Q).subtype) g =
      localIntegralCharacter u Q g := by
  change (localIntegralCharacter u Q g *
      (IsNonarchimedeanLocalField.teichmullerCharacter E p
        ((residualCharacter u).comp (primeDecompositionGroup Q).subtype) g)⁻¹) *
      IsNonarchimedeanLocalField.teichmullerCharacter E p
        ((residualCharacter u).comp (primeDecompositionGroup Q).subtype) g =
      localIntegralCharacter u Q g
  group

omit [NumberField F] [NormedAlgebra ℚ_[p] E] in
/-- The Teichmüller lift preserves pointwise products of residual characters. -/
theorem teichmullerCharacter_residualCharacterProduct
    {G : Type*} [Group G]
    (χ η : G →* (𝒪[E] ⧸ 𝓂[E])ˣ) (g : G) :
    IsNonarchimedeanLocalField.teichmullerCharacter E p
      (residualCharacterProduct χ η) g =
    IsNonarchimedeanLocalField.teichmullerCharacter E p χ g *
      IsNonarchimedeanLocalField.teichmullerCharacter E p η g := by
  change Ideal.teichmullerUnits 𝓂[E] p (χ g * η g) =
    Ideal.teichmullerUnits 𝓂[E] p (χ g) *
      Ideal.teichmullerUnits 𝓂[E] p (η g)
  exact map_mul (Ideal.teichmullerUnits 𝓂[E] p) (χ g) (η g)

/-- Multiply the old ordinary factor by the normalized local twist. -/
def localOrdinaryTwistCharacter
    {Q : Ideal (𝓞 (AlgebraicClosure F))}
    (ψ : primeDecompositionGroup Q →* 𝒪[E]ˣ)
    (u : AbsoluteGalois F →* 𝒪[E]ˣ) :
    primeDecompositionGroup Q →* 𝒪[E]ˣ where
  toFun g := ψ g * localNormalizedTwistCharacter p u Q g
  map_one' := by simp
  map_mul' g h := by simp only [map_mul]; ac_rfl

omit [NumberField F] [NormedAlgebra ℚ_[p] E] in
@[simp]
theorem localOrdinaryTwistCharacter_apply
    {Q : Ideal (𝓞 (AlgebraicClosure F))}
    (ψ : primeDecompositionGroup Q →* 𝒪[E]ˣ)
    (u : AbsoluteGalois F →* 𝒪[E]ˣ)
    (g : primeDecompositionGroup Q) :
    localOrdinaryTwistCharacter p ψ u g =
      ψ g * localNormalizedTwistCharacter p u Q g := (rfl)

omit [NumberField F] [NormedAlgebra ℚ_[p] E] in
/-- A finite integral character still has finite range after local
Teichmüller normalization. -/
theorem localNormalizedTwistCharacter_finite_range
    (u : AbsoluteGalois F →* 𝒪[E]ˣ)
    (hu : (Set.range u).Finite)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) :
    (Set.range (localNormalizedTwistCharacter p u Q)).Finite := by
  have huQ : (Set.range (localIntegralCharacter u Q)).Finite :=
    hu.subset (by
      rintro _ ⟨g, rfl⟩
      exact ⟨(g : AbsoluteGalois F), rfl⟩)
  exact Ideal.finite_range_teichmullerNormalizedCharacter 𝓂[E] p
    (localIntegralCharacter u Q) huQ

omit [NumberField F] [NormedAlgebra ℚ_[p] E] in
/-- Continuity of local normalization follows from continuity of the
integral finite character. -/
theorem localNormalizedTwistCharacter_continuous
    (u : AbsoluteGalois F →* 𝒪[E]ˣ)
    (hu : Continuous u)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) :
    Continuous (localNormalizedTwistCharacter p u Q) := by
  have huQ : Continuous (localIntegralCharacter u Q) :=
    hu.comp continuous_subtype_val
  let : DiscreteTopology (𝒪[E] ⧸ 𝓂[E]) :=
    QuotientAddGroup.discreteTopology (IsLocalRing.isOpen_maximalIdeal 𝒪[E])
  exact Ideal.continuous_teichmullerNormalizedCharacter 𝓂[E] p
    (localIntegralCharacter u Q) huQ

omit [NumberField F] [NormedAlgebra ℚ_[p] E] in
/-- The normalized local factor gives precisely the new diagonal entry after
the residual character is multiplied by the reduction of the twist. -/
theorem localOrdinaryTwistCharacter_diagonal
    (Q : Ideal (𝓞 (AlgebraicClosure F)))
    (ψ : primeDecompositionGroup Q →* 𝒪[E]ˣ)
    (χ : primeDecompositionGroup Q →* (𝒪[E] ⧸ 𝓂[E])ˣ)
    (u : AbsoluteGalois F →* 𝒪[E]ˣ)
    (g : primeDecompositionGroup Q) :
    ((localIntegralCharacter u Q g : 𝒪[E]) : E) *
      (((ψ g : 𝒪[E]) : E) *
        ((IsNonarchimedeanLocalField.teichmullerCharacter E p χ g : 𝒪[E]) : E)) =
    ((localOrdinaryTwistCharacter p ψ u g : 𝒪[E]) : E) *
      ((IsNonarchimedeanLocalField.teichmullerCharacter E p
        (residualCharacterProduct χ
          ((residualCharacter u).comp (primeDecompositionGroup Q).subtype)) g :
        𝒪[E]) : E) := by
  have ht := teichmullerCharacter_residualCharacterProduct p χ
    ((residualCharacter u).comp (primeDecompositionGroup Q).subtype) g
  have hn := localNormalizedTwistCharacter_mul_teichmuller p u Q g
  have hunit : localIntegralCharacter u Q g * ψ g *
      IsNonarchimedeanLocalField.teichmullerCharacter E p χ g =
      localOrdinaryTwistCharacter p ψ u g *
      IsNonarchimedeanLocalField.teichmullerCharacter E p
          (residualCharacterProduct χ
            ((residualCharacter u).comp (primeDecompositionGroup Q).subtype)) g := by
    rw [← hn, localOrdinaryTwistCharacter_apply, ht]
    let a := localNormalizedTwistCharacter p u Q g
    let b := IsNonarchimedeanLocalField.teichmullerCharacter E p
      ((residualCharacter u).comp (primeDecompositionGroup Q).subtype) g
    let c := ψ g
    let d := IsNonarchimedeanLocalField.teichmullerCharacter E p χ g
    change a * b * c * d = c * a * (d * b)
    calc
      a * b * c * d = c * (a * b) * d := by rw [mul_comm (a * b) c]
      _ = c * a * (b * d) := by simp only [mul_assoc]
      _ = c * a * (d * b) := by rw [mul_comm b d]
  have := congrArg (fun v : 𝒪[E]ˣ => ((v : 𝒪[E]) : E)) hunit
  simpa only [Units.val_mul, Subring.coe_mul, mul_assoc] using this

/-- Twisting an adapted ordinary basis changes each normalized diagonal
character by the principal-unit part of the finite twist. -/
def SkinnerWilesOrdinaryAt.characterTwist
    {ρ : Representation E (AbsoluteGalois F) (Fin 2 → E)}
    {D : SkinnerWilesResidualData ρ}
    {Q : Ideal (𝓞 (AlgebraicClosure F))} [Q.IsMaximal]
    (H : SkinnerWilesOrdinaryAt p ρ D Q)
    (u : AbsoluteGalois F →* 𝒪[E]ˣ)
    (hu : (Set.range u).Finite) (huc : Continuous u) :
    SkinnerWilesOrdinaryAt p
      (ρ.characterTwist (integralCharacterToField u))
      (D.characterTwist u) Q where
  basis := H.basis
  psi₁ := localOrdinaryTwistCharacter p H.psi₁ u
  psi₂ := localOrdinaryTwistCharacter p H.psi₂ u
  psi₂_continuous :=
    H.psi₂_continuous.mul (localNormalizedTwistCharacter_continuous p u huc Q)
  psi₂_reduction := by
    intro g
    change Units.map (Ideal.Quotient.mk 𝓂[E] : 𝒪[E] →* 𝒪[E] ⧸ 𝓂[E])
      (H.psi₂ g * localNormalizedTwistCharacter p u Q g) = 1
    simp [H.psi₂_reduction g, localNormalizedTwistCharacter_reduction]
  psi₂_pro_p := by
    intro T _ _ _ f hf
    exact isPGroup_range_principalCharacter p
      (localOrdinaryTwistCharacter p H.psi₂ u)
      (by intro g; simp [H.psi₂_reduction g,
        localNormalizedTwistCharacter_reduction]) f hf
  psi₂_finite_inertia := by
    let S : Set 𝒪[E]ˣ := {a | ∃ g : primeDecompositionGroup Q,
      (g : AbsoluteGalois F) ∈ Q.inertia (AbsoluteGalois F) ∧ H.psi₂ g = a}
    let T : Set 𝒪[E]ˣ := Set.range (localNormalizedTwistCharacter p u Q)
    have hS : S.Finite := H.psi₂_finite_inertia
    have hT : T.Finite := localNormalizedTwistCharacter_finite_range p u hu Q
    have hprod : (S ×ˢ T).Finite := hS.prod hT
    apply (hprod.image (fun z : 𝒪[E]ˣ × 𝒪[E]ˣ => z.1 * z.2)).subset
    rintro a ⟨g, hg, rfl⟩
    exact ⟨(H.psi₂ g, localNormalizedTwistCharacter p u Q g),
      ⟨⟨g, hg, rfl⟩, ⟨g, rfl⟩⟩, rfl⟩
  lower_left_zero := by
    intro g
    rw [Representation.characterTwist_apply, map_smul, Pi.smul_apply,
      H.lower_left_zero]
    simp
  upper_left := by
    intro g
    rw [Representation.characterTwist_apply, map_smul, Pi.smul_apply,
      H.upper_left]
    exact localOrdinaryTwistCharacter_diagonal p Q H.psi₁
      (D.chi₁.comp (primeDecompositionGroup Q).subtype) u g
  lower_right := by
    intro g
    rw [Representation.characterTwist_apply, map_smul, Pi.smul_apply,
      H.lower_right]
    exact localOrdinaryTwistCharacter_diagonal p Q H.psi₂
      (D.chi₂.comp (primeDecompositionGroup Q).subtype) u g

/-- A finite integral scalar twist preserves the full weight-two
Skinner--Wiles checklist. The twisting character's finite ramification set
and inertia condition are explicit inputs, so the enlarged bad set is exactly
the union of the two given sets. -/
def SkinnerWilesWeightTwoInput.characterTwist
    {ρ : Representation E (AbsoluteGalois F) (Fin 2 → E)}
    {L : Type*} [Field L] [NumberField L] [Algebra F L]
    (H : SkinnerWilesWeightTwoInput p ρ L)
    (u : AbsoluteGalois F →* 𝒪[E]ˣ)
    (hu : (Set.range u).Finite) (huc : Continuous u)
    (ramified_u : Set (HeightOneSpectrum (𝓞 F)))
    (hru : ramified_u.Finite)
    (hunramified : ∀ q, q ∉ ramified_u →
      ∀ (P : Ideal (𝓞 F)) [P.IsMaximal], P = q.asIdeal →
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
      ∀ g : AbsoluteGalois F, g ∈ Q.inertia (AbsoluteGalois F) → u g = 1) :
    SkinnerWilesWeightTwoInput p
      (ρ.characterTwist (integralCharacterToField u)) L where
  p_odd := H.p_odd
  totally_real := H.totally_real
  galois_over_rat := H.galois_over_rat
  abelian_over_rat := H.abelian_over_rat
  continuous := by
    intro i j
    have hval : Continuous (fun z : Eˣ => (z : E)) := by fun_prop
    have hc : Continuous (fun g : AbsoluteGalois F =>
        ((integralCharacterToField u g : Eˣ) : E)) :=
      hval.comp (continuous_integralCharacterToField u huc)
    have hfun : (fun g : AbsoluteGalois F =>
        (ρ.characterTwist (integralCharacterToField u)) g (Pi.single j 1) i) =
        (fun g : AbsoluteGalois F =>
          ((integralCharacterToField u g : Eˣ) : E) *
            ρ g (Pi.single j 1) i) := by
      funext g
      simp [Representation.characterTwist_apply, Pi.smul_apply, smul_eq_mul]
    rw [hfun]
    exact hc.mul (H.continuous i j)
  absolutely_irreducible := by
    let : (ρ.baseChange (AlgebraicClosure E)).IsIrreducible :=
      H.absolutely_irreducible
    rw [Representation.baseChange_characterTwist]
    exact Representation.isIrreducible_characterTwist _ _
  ramified := H.ramified ∪ ramified_u
  ramified_finite := H.ramified_finite.union hru
  unramified := by
    intro q hq P hP hPeq Q hQ hL g hg
    simp only [Set.mem_union, not_or] at hq
    have hρ := H.unramified q hq.1 P hPeq Q g hg
    have huu := hunramified q hq.2 P hPeq Q g hg
    ext v
    simp [Representation.characterTwist_apply, integralCharacterToField,
      hρ, huu]
  residual := H.residual.characterTwist u
  ratio_field := H.ratio_field.characterTwist u
  ratio_odd := by
    intro c hc
    simpa only [residualRatio_characterTwist] using H.ratio_odd c hc
  local_ordinary := by
    intro P hP hp Q hQ hL
    exact (H.local_ordinary P hp Q).characterTwist p u hu huc
  ratio_distinguished := by
    intro P hP hp Q hQ hL
    obtain ⟨g, hg⟩ := H.ratio_distinguished P hp Q
    exact ⟨g, by simpa only [residualRatio_characterTwist] using hg⟩
  finite_det_character := determinantCharacterTwist H.finite_det_character u
  finite_det_range :=
    finite_range_determinantCharacterTwist H.finite_det_character u
      H.finite_det_range hu
  determinant := by
    intro g
    rw [det_characterTwist, H.determinant]
    change (integralCharacterToField u g : E) ^ 2 *
      ((H.finite_det_character g : E) *
        (Field.cyclotomicCharacterWithCoefficients F p E g : E)) =
      ((H.finite_det_character g : E) * (integralCharacterToField u g : E) ^ 2) *
        (Field.cyclotomicCharacterWithCoefficients F p E g : E)
    ring


end HilbertModularity.HilbertModularForms
