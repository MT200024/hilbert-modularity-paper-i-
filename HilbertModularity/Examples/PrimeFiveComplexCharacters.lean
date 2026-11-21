/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Examples.PrimeFiveOrientedCharacter
public import HilbertModularity.Examples.PrimeFiveHypergeometric

/-! # The worked example's actual complex character labels

An oriented cyclotomic residue prime and a complex embedding of the fixed
cyclotomic coefficient field transport the canonical positive power-residue
character to the character used in the direct McCarthy evaluation.
-/

public noncomputable section

open IsDedekindDomain
open scoped NumberField

namespace HilbertModularity.Examples

open _root_.HilbertModularity.Cyclotomic

attribute [local instance] Ideal.Quotient.field
local instance complexCharacterFiveFact : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance complexCharacterElevenFact : Fact (Nat.Prime 11) := ⟨by decide⟩
local instance complexCharacterFortyOneFact : Fact (Nat.Prime 41) := ⟨by decide⟩

/-- The positive fifth root as an element of the set of primitive roots. -/
def primeFiveComplexRoot : primitiveRoots 5 ℂ :=
  ⟨fifthRoot, (mem_primitiveRoots (by decide)).mpr fifthRoot_isPrimitiveRoot⟩

/-- Embeddings of the fixed cyclotomic field are classified by the image of
its chosen primitive root. -/
def primeFiveComplexEmbeddings :
    (cyclotomicField 5 →ₐ[ℚ] ℂ) ≃ primitiveRoots 5 ℂ :=
  (root_isPrimitiveRoot 5).embeddingsEquivPrimitiveRoots ℂ
    (Polynomial.cyclotomic.irreducible_rat (by decide))

/-- The coefficient embedding carrying the chosen algebraic fifth root to
the positive complex fifth root used in the direct Gauss-sum evaluation. -/
def primeFiveComplexEmbedding : cyclotomicField 5 →+* ℂ :=
  (primeFiveComplexEmbeddings.symm primeFiveComplexRoot).toRingHom

/-- This embedding realizes the manuscript's stated choice of ζ₅. -/
theorem primeFiveComplexEmbedding_root :
    primeFiveComplexEmbedding (root 5) = fifthRoot := by
  have h : ((primeFiveComplexEmbeddings
      (primeFiveComplexEmbeddings.symm primeFiveComplexRoot) :
        primitiveRoots 5 ℂ) : ℂ) =
      (primeFiveComplexEmbeddings.symm primeFiveComplexRoot) (root 5) :=
    (root_isPrimitiveRoot 5).embeddingsEquivPrimitiveRoots_apply_coe
      ℂ (Polynomial.cyclotomic.irreducible_rat (by decide)) _
  have he := primeFiveComplexEmbeddings.apply_symm_apply primeFiveComplexRoot
  change (primeFiveComplexEmbeddings.symm primeFiveComplexRoot) (root 5) = fifthRoot
  exact h.symm.trans (congrArg Subtype.val he)

/-- The canonical cyclotomic character at an oriented prime, transported
through its actual residue equivalence and the chosen complex embedding. -/
def primeFiveComplexCharacter11
    (P : Ideal (𝓞 (cyclotomicField 5))) [P.IsMaximal]
    (hP : (5 : 𝓞 (cyclotomicField 5)) ∉ P)
    (e : (𝓞 (cyclotomicField 5) ⧸ P) ≃+* ZMod 11)
    (ι : cyclotomicField 5 →+* ℂ) : MulChar (ZMod 11) ℂ :=
  MulChar.ofUnitHom
    ((Units.map (ι : cyclotomicField 5 →* ℂ)).comp
      ((cyclotomicPowerResidueMulChar 5 P hP).toUnitHom.comp
        (Units.map e.symm.toRingHom.toMonoidHom)))

/-- Pointwise transport of the actual cyclotomic residue character to the
eleven-element field, including its zero value. -/
theorem primeFiveComplexCharacter11_apply
    (P : Ideal (𝓞 (cyclotomicField 5))) [P.IsMaximal]
    (hP : (5 : 𝓞 (cyclotomicField 5)) ∉ P)
    (e : (𝓞 (cyclotomicField 5) ⧸ P) ≃+* ZMod 11)
    (ι : cyclotomicField 5 →+* ℂ) (x : ZMod 11) :
    primeFiveComplexCharacter11 P hP e ι x =
      ι (cyclotomicPowerResidueMulChar 5 P hP (e.symm x)) := by
  by_cases hx : x = 0
  · subst x
    simp only [MulChar.map_zero, map_zero]
  · let u : (ZMod 11)ˣ := Units.mk0 x hx
    change primeFiveComplexCharacter11 P hP e ι u =
      ι (cyclotomicPowerResidueMulChar 5 P hP (e.symm u))
    simp only [primeFiveComplexCharacter11, MulChar.ofUnitHom_coe,
      MonoidHom.comp_apply]
    rw [Units.coe_map]
    change ι (cyclotomicPowerResidueMulChar 5 P hP
      ((Units.map e.symm.toRingHom.toMonoidHom) u : 𝓞 (cyclotomicField 5) ⧸ P)) = _
    rw [Units.coe_map]
    rfl

/-- The actual transported character has the manuscript's fixed label
`A₁₁(2)=ζ₅` under the specified coefficient embedding. -/
theorem primeFiveComplexCharacter11_generator
    (P : Ideal (𝓞 (cyclotomicField 5))) [P.IsMaximal]
    (hP : (5 : 𝓞 (cyclotomicField 5)) ∉ P)
    (e : (𝓞 (cyclotomicField 5) ⧸ P) ≃+* ZMod 11)
    (he : e (Ideal.Quotient.mk P (rootInteger 5)) = 4)
    (ι : cyclotomicField 5 →+* ℂ) (hι : ι (root 5) = fifthRoot) :
    primeFiveComplexCharacter11 P hP e ι 2 = fifthRoot := by
  let u : (ZMod 11)ˣ := Units.mk0 2 (by decide)
  change primeFiveComplexCharacter11 P hP e ι u = fifthRoot
  simp only [primeFiveComplexCharacter11, MulChar.ofUnitHom_coe,
    MonoidHom.comp_apply]
  rw [Units.coe_map]
  change ι (cyclotomicPowerResidueMulChar 5 P hP
    ((Units.map e.symm.toRingHom.toMonoidHom) u : 𝓞 (cyclotomicField 5) ⧸ P)) = fifthRoot
  rw [Units.coe_map]
  change ι (cyclotomicPowerResidueMulChar 5 P hP (e.symm 2)) = fifthRoot
  exact
    (congrArg ι (primeFive_orientedCyclotomicCharacter_11 P hP e he)).trans hι

/-- The actual oriented character at eleven has exact order five. -/
theorem primeFiveComplexCharacter11_orderOf
    (P : Ideal (𝓞 (cyclotomicField 5))) [P.IsMaximal]
    (hP : (5 : 𝓞 (cyclotomicField 5)) ∉ P)
    (e : (𝓞 (cyclotomicField 5) ⧸ P) ≃+* ZMod 11)
    (he : e (Ideal.Quotient.mk P (rootInteger 5)) = 4) :
    orderOf (primeFiveComplexCharacter11 P hP e primeFiveComplexEmbedding) = 5 := by
  have hg : orderOf generator11 = Fintype.card (ZMod 11)ˣ := by
    rw [← generator11_isPrimitiveRoot.eq_orderOf, ZMod.card_units]
  have hgen : ∀ x, x ∈ Subgroup.zpowers generator11 := by
    have ht : Subgroup.zpowers generator11 = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by simpa only [Nat.card_eq_fintype_card,
        Fintype.card_zpowers] using hg)
    simp [ht]
  rw [← MulChar.orderOf_apply_generator _ hgen]
  change orderOf (primeFiveComplexCharacter11 P hP e primeFiveComplexEmbedding 2) = 5
  rw [primeFiveComplexCharacter11_generator P hP e he _ primeFiveComplexEmbedding_root]
  exact fifthRoot_isPrimitiveRoot.eq_orderOf.symm

/-- The canonical cyclotomic character at the oriented prime above forty-one,
transported into the complex coefficient field. -/
def primeFiveComplexCharacter41
    (P : Ideal (𝓞 (cyclotomicField 5))) [P.IsMaximal]
    (hP : (5 : 𝓞 (cyclotomicField 5)) ∉ P)
    (e : (𝓞 (cyclotomicField 5) ⧸ P) ≃+* ZMod 41)
    (ι : cyclotomicField 5 →+* ℂ) : MulChar (ZMod 41) ℂ :=
  MulChar.ofUnitHom
    ((Units.map (ι : cyclotomicField 5 →* ℂ)).comp
      ((cyclotomicPowerResidueMulChar 5 P hP).toUnitHom.comp
        (Units.map e.symm.toRingHom.toMonoidHom)))

/-- Pointwise transport at forty-one under the same complex embedding. -/
theorem primeFiveComplexCharacter41_apply
    (P : Ideal (𝓞 (cyclotomicField 5))) [P.IsMaximal]
    (hP : (5 : 𝓞 (cyclotomicField 5)) ∉ P)
    (e : (𝓞 (cyclotomicField 5) ⧸ P) ≃+* ZMod 41)
    (ι : cyclotomicField 5 →+* ℂ) (x : ZMod 41) :
    primeFiveComplexCharacter41 P hP e ι x =
      ι (cyclotomicPowerResidueMulChar 5 P hP (e.symm x)) := by
  by_cases hx : x = 0
  · subst x
    simp only [MulChar.map_zero, map_zero]
  · let u : (ZMod 41)ˣ := Units.mk0 x hx
    change primeFiveComplexCharacter41 P hP e ι u =
      ι (cyclotomicPowerResidueMulChar 5 P hP (e.symm u))
    simp only [primeFiveComplexCharacter41, MulChar.ofUnitHom_coe,
      MonoidHom.comp_apply]
    rw [Units.coe_map]
    change ι (cyclotomicPowerResidueMulChar 5 P hP
      ((Units.map e.symm.toRingHom.toMonoidHom) u : 𝓞 (cyclotomicField 5) ⧸ P)) = _
    rw [Units.coe_map]
    rfl

/-- The same oriented power convention gives `A₄₁(6)=ζ₅`. -/
theorem primeFiveComplexCharacter41_generator
    (P : Ideal (𝓞 (cyclotomicField 5))) [P.IsMaximal]
    (hP : (5 : 𝓞 (cyclotomicField 5)) ∉ P)
    (e : (𝓞 (cyclotomicField 5) ⧸ P) ≃+* ZMod 41)
    (he : e (Ideal.Quotient.mk P (rootInteger 5)) = 10)
    (ι : cyclotomicField 5 →+* ℂ) (hι : ι (root 5) = fifthRoot) :
    primeFiveComplexCharacter41 P hP e ι 6 = fifthRoot := by
  let u : (ZMod 41)ˣ := Units.mk0 6 (by decide)
  change primeFiveComplexCharacter41 P hP e ι u = fifthRoot
  simp only [primeFiveComplexCharacter41, MulChar.ofUnitHom_coe,
    MonoidHom.comp_apply]
  rw [Units.coe_map]
  change ι (cyclotomicPowerResidueMulChar 5 P hP
    ((Units.map e.symm.toRingHom.toMonoidHom) u : 𝓞 (cyclotomicField 5) ⧸ P)) = fifthRoot
  rw [Units.coe_map]
  change ι (cyclotomicPowerResidueMulChar 5 P hP (e.symm 6)) = fifthRoot
  exact
    (congrArg ι (primeFive_orientedCyclotomicCharacter_41 P hP e he)).trans hι

/-- The actual oriented character at forty-one has exact order five. -/
theorem primeFiveComplexCharacter41_orderOf
    (P : Ideal (𝓞 (cyclotomicField 5))) [P.IsMaximal]
    (hP : (5 : 𝓞 (cyclotomicField 5)) ∉ P)
    (e : (𝓞 (cyclotomicField 5) ⧸ P) ≃+* ZMod 41)
    (he : e (Ideal.Quotient.mk P (rootInteger 5)) = 10) :
    orderOf (primeFiveComplexCharacter41 P hP e primeFiveComplexEmbedding) = 5 := by
  have hg : orderOf generator41 = Fintype.card (ZMod 41)ˣ := by
    rw [← generator41_isPrimitiveRoot.eq_orderOf, ZMod.card_units]
  have hgen : ∀ x, x ∈ Subgroup.zpowers generator41 := by
    have ht : Subgroup.zpowers generator41 = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by simpa only [Nat.card_eq_fintype_card,
        Fintype.card_zpowers] using hg)
    simp [ht]
  rw [← MulChar.orderOf_apply_generator _ hgen]
  change orderOf (primeFiveComplexCharacter41 P hP e primeFiveComplexEmbedding 6) = 5
  rw [primeFiveComplexCharacter41_generator P hP e he _ primeFiveComplexEmbedding_root]
  exact fifthRoot_isPrimitiveRoot.eq_orderOf.symm

/-- Direct McCarthy evaluation on the actual oriented cyclotomic residue
character at eleven. The additive character is any nontrivial choice. -/
theorem primeFiveComplexCharacter11_mccarthyValue
    (P : Ideal (𝓞 (cyclotomicField 5))) [P.IsMaximal]
    (hP : (5 : 𝓞 (cyclotomicField 5)) ∉ P)
    (e : (𝓞 (cyclotomicField 5) ⧸ P) ≃+* ZMod 11)
    (he : e (Ideal.Quotient.mk P (rootInteger 5)) = 4)
    (θ : AddChar (ZMod 11) ℂ) (hθ : θ ≠ 1) :
    Hypergeometric.rankTwoMcCarthySum θ
      (primeFiveComplexCharacter11 P hP e primeFiveComplexEmbedding) 125 =
        ((Real.sqrt 5 : ℂ) - 1) / 2 :=
  rankTwoMcCarthySum_11_eq_sqrt _
    (primeFiveComplexCharacter11_generator P hP e he _ primeFiveComplexEmbedding_root)
    θ hθ

/-- Direct McCarthy evaluation at forty-one under the same positive power
residue convention and the same complex coefficient embedding. -/
theorem primeFiveComplexCharacter41_mccarthyValue
    (P : Ideal (𝓞 (cyclotomicField 5))) [P.IsMaximal]
    (hP : (5 : 𝓞 (cyclotomicField 5)) ∉ P)
    (e : (𝓞 (cyclotomicField 5) ⧸ P) ≃+* ZMod 41)
    (he : e (Ideal.Quotient.mk P (rootInteger 5)) = 10)
    (θ : AddChar (ZMod 41) ℂ) (hθ : θ ≠ 1) :
    Hypergeometric.rankTwoMcCarthySum θ
      (primeFiveComplexCharacter41 P hP e primeFiveComplexEmbedding) 125 =
        (-1 - 5 * (Real.sqrt 5 : ℂ)) / 2 :=
  rankTwoMcCarthySum_41_eq_sqrt _
    (primeFiveComplexCharacter41_generator P hP e he _ primeFiveComplexEmbedding_root)
    θ hθ

/-- An actual oriented cyclotomic prime above eleven realizes the direct
McCarthy value for every nontrivial additive character. -/
theorem exists_primeFive_orientedMcCarthyValue_11
    (θ : AddChar (ZMod 11) ℂ) (hθ : θ ≠ 1) :
    ∃ P : HeightOneSpectrum (𝓞 (cyclotomicField 5)),
      ∃ hP : (5 : 𝓞 (cyclotomicField 5)) ∉ P.asIdeal,
        ∃ e : (𝓞 (cyclotomicField 5) ⧸ P.asIdeal) ≃+* ZMod 11,
          e (Ideal.Quotient.mk P.asIdeal (rootInteger 5)) = 4 ∧
          Hypergeometric.rankTwoMcCarthySum θ
            (primeFiveComplexCharacter11 P.asIdeal hP e primeFiveComplexEmbedding) 125 =
              ((Real.sqrt 5 : ℂ) - 1) / 2 := by
  obtain ⟨P, hP, e, he⟩ := exists_primeFive_orientedPrime_11
  exact ⟨P, hP, e, he, primeFiveComplexCharacter11_mccarthyValue
    P.asIdeal hP e he θ hθ⟩

/-- The corresponding actual prime above forty-one yields the second
direct McCarthy value with the same coefficient embedding. -/
theorem exists_primeFive_orientedMcCarthyValue_41
    (θ : AddChar (ZMod 41) ℂ) (hθ : θ ≠ 1) :
    ∃ P : HeightOneSpectrum (𝓞 (cyclotomicField 5)),
      ∃ hP : (5 : 𝓞 (cyclotomicField 5)) ∉ P.asIdeal,
        ∃ e : (𝓞 (cyclotomicField 5) ⧸ P.asIdeal) ≃+* ZMod 41,
          e (Ideal.Quotient.mk P.asIdeal (rootInteger 5)) = 10 ∧
          Hypergeometric.rankTwoMcCarthySum θ
            (primeFiveComplexCharacter41 P.asIdeal hP e primeFiveComplexEmbedding) 125 =
              (-1 - 5 * (Real.sqrt 5 : ℂ)) / 2 := by
  obtain ⟨P, hP, e, he⟩ := exists_primeFive_orientedPrime_41
  exact ⟨P, hP, e, he, primeFiveComplexCharacter41_mccarthyValue
    P.asIdeal hP e he θ hθ⟩

end HilbertModularity.Examples
