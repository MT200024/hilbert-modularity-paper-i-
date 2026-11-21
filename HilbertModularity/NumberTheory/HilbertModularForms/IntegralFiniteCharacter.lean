/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.HilbertModularForms.SkinnerWilesCharacterTwist

/-! # Integral values of finite Galois characters

A finite-order character valued in a nonarchimedean local field takes values
in its valuation-ring units. This supplies the integral character required by
the residual and local ordinary calculations for [SkinnerWiles, §4.5,
Theorem A].
-/

public noncomputable section

open scoped ValuativeRel
open ValuativeRel

namespace HilbertModularity.HilbertModularForms

variable {G E : Type*} [Group G] [NormedField E] [ValuativeRel E]
  [IsNonarchimedeanLocalField E]

omit [ValuativeRel E] [IsNonarchimedeanLocalField E] in
private theorem finiteCharacter_value_finiteOrder
    (ν : G →* Eˣ) (hν : (Set.range ν).Finite) (g : G) :
    IsOfFinOrder (ν g) := by
  apply finite_powers.mp
  apply hν.subset
  intro x hx
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff x (ν g)).mp hx
  exact ⟨g ^ n, map_pow ν g n⟩

private theorem finiteCharacter_value_integral
    (ν : G →* Eˣ) (hν : (Set.range ν).Finite) (g : G) :
    (ν g : E) ∈ 𝒪[E] := by
  have hval : IsOfFinOrder ((Valued.v) (ν g : E)) :=
    (Valued.v).isOfFinOrder
      (Units.isOfFinOrder_val.mpr (finiteCharacter_value_finiteOrder ν hν g))
  exact (Valuation.mem_integer_iff (Valued.v) _).mpr hval.eq_one'.le

private def finiteCharacter_integralUnit
    (ν : G →* Eˣ) (hν : (Set.range ν).Finite) (g : G) : 𝒪[E]ˣ where
  val := ⟨(ν g : E), finiteCharacter_value_integral ν hν g⟩
  inv := ⟨(ν g⁻¹ : E), finiteCharacter_value_integral ν hν g⁻¹⟩
  val_inv := by
    apply Subtype.ext
    change (ν g : E) * (ν g⁻¹ : E) = 1
    simp
  inv_val := by
    apply Subtype.ext
    change (ν g⁻¹ : E) * (ν g : E) = 1
    simp

/-- Lift a finite-image character from field units to valuation-ring units. -/
def finiteCharacterIntegralLift (ν : G →* Eˣ)
    (hν : (Set.range ν).Finite) : G →* 𝒪[E]ˣ where
  toFun := finiteCharacter_integralUnit ν hν
  map_one' := by
    apply Units.ext
    apply Subtype.ext
    simp [finiteCharacter_integralUnit]
  map_mul' g h := by
    apply Units.ext
    apply Subtype.ext
    simp [finiteCharacter_integralUnit]

/-- The integral lift recovers the original field-valued character exactly. -/
@[simp]
theorem finiteCharacterIntegralLift_toField (ν : G →* Eˣ)
    (hν : (Set.range ν).Finite) (g : G) :
    (Units.map (algebraMap 𝒪[E] E : 𝒪[E] →* E))
      (finiteCharacterIntegralLift ν hν g) = ν g := by
  apply Units.ext
  rfl

/-- The lift has finite image because valuation-ring units embed in field
units. -/
theorem finiteCharacterIntegralLift_finite_range
    (ν : G →* Eˣ) (hν : (Set.range ν).Finite) :
    (Set.range (finiteCharacterIntegralLift ν hν)).Finite := by
  let f : 𝒪[E]ˣ → Eˣ :=
    Units.map (algebraMap 𝒪[E] E : 𝒪[E] →* E)
  have hf : Function.Injective f := by
    intro a b hab
    apply Units.ext
    apply Subtype.ext
    exact congrArg (fun x : Eˣ => (x : E)) hab
  apply Set.Finite.of_finite_image (f := f)
  · apply hν.subset
    rintro x ⟨u, ⟨g, rfl⟩, rfl⟩
    exact ⟨g, (finiteCharacterIntegralLift_toField ν hν g).symm⟩
  · intro a _ b _ hab
    exact hf hab

omit [ValuativeRel E] [IsNonarchimedeanLocalField E] in
/-- Inverting a finite-image field-valued character preserves finite image. -/
theorem finiteCharacter_inverse_finite_range
    (ν : G →* Eˣ) (hν : (Set.range ν).Finite) :
    (Set.range ν⁻¹).Finite := by
  apply (hν.image (fun z : Eˣ => z⁻¹)).subset
  rintro x ⟨g, rfl⟩
  exact ⟨ν g, ⟨g, rfl⟩, by simp⟩

omit [ValuativeRel E] [IsNonarchimedeanLocalField E] in
/-- Inverting a continuous field-valued character preserves continuity. -/
theorem continuous_finiteCharacter_inverse [TopologicalSpace G]
    (ν : G →* Eˣ) (hνc : Continuous ν) : Continuous ν⁻¹ := by
  change Continuous (fun g : G => (ν g)⁻¹)
  exact continuous_inv.comp hνc

/-- A value is trivial exactly when its integral lift is trivial. -/
@[simp]
theorem finiteCharacterIntegralLift_apply_eq_one_iff
    (ν : G →* Eˣ) (hν : (Set.range ν).Finite) (g : G) :
    finiteCharacterIntegralLift ν hν g = 1 ↔ ν g = 1 := by
  constructor
  · intro h
    have hm := congrArg
      (Units.map (algebraMap 𝒪[E] E : 𝒪[E] →* E)) h
    simpa only [map_one, finiteCharacterIntegralLift_toField] using hm
  · intro h
    apply Units.ext
    apply Subtype.ext
    exact congrArg (fun x : Eˣ => (x : E)) h

/-- Continuity passes to the integral lift with the subspace topology of
the valuation ring. -/
theorem continuous_finiteCharacterIntegralLift [TopologicalSpace G]
    (ν : G →* Eˣ) (hν : (Set.range ν).Finite) (hνc : Continuous ν) :
    Continuous (finiteCharacterIntegralLift ν hν) := by
  apply Units.continuous_iff.mpr
  constructor
  · change Continuous (fun g : G =>
      (⟨(ν g : E), finiteCharacter_value_integral ν hν g⟩ : 𝒪[E]))
    exact (Units.continuous_val.comp hνc).subtype_mk _
  · change Continuous (fun g : G =>
      (⟨(ν g⁻¹ : E), finiteCharacter_value_integral ν hν g⁻¹⟩ : 𝒪[E]))
    apply Continuous.subtype_mk
    have hi : Continuous (fun g : G => (ν g)⁻¹) := continuous_inv.comp hνc
    convert Units.continuous_val.comp hi using 1
    funext g
    simp [map_inv]

end HilbertModularity.HilbertModularForms
