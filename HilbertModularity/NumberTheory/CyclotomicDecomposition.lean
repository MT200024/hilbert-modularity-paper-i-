/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.CyclotomicGalois
public import HilbertModularity.NumberTheory.RealCyclotomicResidue
public import HilbertModularity.NumberTheory.GaloisPrimes

/-! # The residual cyclotomic character at the ramified prime

The decomposition group at the conductor contains a lift of cyclotomic
conjugation. Consequently the residual character over the real cyclotomic
field has exact order two on that group, as used in [TripathiGoswami].
-/

@[expose] public noncomputable section

open scoped NumberField Pointwise

namespace HilbertModularity.Cyclotomic

variable (p : ℕ) [Fact p.Prime]

/-- Any prime of the algebraic integers containing `p` lies above the
unique cyclotomic prime of conductor `p`. -/
theorem liesOver_primeAboveConductor_of_mem (Q : Ideal (𝓞 Qbar)) [Q.IsPrime]
    (hp : (p : 𝓞 Qbar) ∈ Q) : Q.LiesOver (primeAboveConductor p).asIdeal := by
  have : (Q.under (𝓞 (cyclotomicField p))).LiesOver (Ideal.span {(p : ℤ)}) := by
    rw [Ideal.liesOver_iff]
    refine Ideal.IsMaximal.eq_of_le (Int.ideal_span_isMaximal_of_prime p)
      Ideal.IsPrime.ne_top' ?_
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, Ideal.mem_under,
      algebraMap_int_eq, map_natCast, map_natCast]
    exact hp
  rw [Ideal.liesOver_iff]
  exact (IsCyclotomicExtension.Rat.eq_span_zeta_sub_one_of_liesOver' p
    (cyclotomicField p) (root_isPrimitiveRoot p) (Q.under (𝓞 (cyclotomicField p)))).symm

/-- The absolute decomposition group at the conductor contains an element
whose residual cyclotomic character is minus one. -/
theorem exists_residualCharacter_eq_neg_one_in_stabilizer
    (Q : Ideal (𝓞 Qbar)) [Q.IsPrime] (hp : (p : 𝓞 Qbar) ∈ Q) :
    ∃ g : MulAction.stabilizer (Qbar ≃ₐ[realCyclotomicField p] Qbar) Q,
      residualCharacter p g = -1 := by
  have := liesOver_primeAboveConductor_of_mem p Q hp
  obtain ⟨g₀, hg₀⟩ := NumberField.RingOfIntegers.exists_stabilizer_lift
    ℚ (cyclotomicField p) Qbar (primeAboveConductor p).asIdeal Q
    (conjugation p) (mem_stabilizer_primeAboveConductor p (conjugation p))
  have hgζ : (g₀ : Qbar ≃ₐ[ℚ] Qbar) (zeta p) = (zeta p)⁻¹ := by
    have h := hg₀ (root p)
    rw [conjugation_root, map_inv₀] at h
    exact h
  have hfix (x : realCyclotomicField p) : (g₀ : Qbar ≃ₐ[ℚ] Qbar) (x : Qbar) = x := by
    have he : (g₀ : Qbar ≃ₐ[ℚ] Qbar).toAlgHom.comp (realCyclotomicField p).val =
        (realCyclotomicField p).val := by
      apply IntermediateField.adjoin_algHom_ext ℚ
      rintro y rfl
      change (g₀ : Qbar ≃ₐ[ℚ] Qbar) (zeta p + (zeta p)⁻¹) = zeta p + (zeta p)⁻¹
      rw [map_add, map_inv₀, hgζ, inv_inv, add_comm]
    exact AlgHom.congr_fun he x
  let g : Qbar ≃ₐ[realCyclotomicField p] Qbar :=
    { __ := (g₀ : Qbar ≃ₐ[ℚ] Qbar).toRingEquiv, commutes' := hfix }
  refine ⟨⟨g, g₀.property⟩, ?_⟩
  exact (zeta_isPrimitiveRoot p).autToPow_eq_neg_one_of_apply_eq_inv g hgζ

/-- At the conductor the residual cyclotomic character has exact order two
on the actual absolute decomposition subgroup. -/
theorem orderOf_residualCharacter_stabilizer [Fact (2 < p)]
    (Q : Ideal (𝓞 Qbar)) [Q.IsPrime] (hp : (p : 𝓞 Qbar) ∈ Q) :
    orderOf ((residualCharacter p).comp
      (MulAction.stabilizer (Qbar ≃ₐ[realCyclotomicField p] Qbar) Q).subtype) = 2 := by
  have : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  apply orderOf_eq_prime
  · apply MonoidHom.ext
    intro g
    exact DFunLike.congr_fun (residualCharacter_sq p) g.val
  · intro h
    obtain ⟨g, hg⟩ := exists_residualCharacter_eq_neg_one_in_stabilizer p Q hp
    have he := DFunLike.congr_fun h g
    change residualCharacter p g = 1 at he
    rw [hg] at he
    exact ZMod.neg_one_ne_one (congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) he)

/-- At the unique prime of the real cyclotomic field above `p`, the residual
character has exact order two. The decomposition group uses any prime of the
algebraic closure above that specified real prime. -/
theorem orderOf_residualCharacter_at_conductor [Fact (2 < p)]
    (Q : Ideal (𝓞 Qbar)) [Q.IsPrime] [Q.LiesOver (realPrimeAboveConductor p).asIdeal] :
    orderOf ((residualCharacter p).comp
      (MulAction.stabilizer (Qbar ≃ₐ[realCyclotomicField p] Qbar) Q).subtype) = 2 := by
  apply orderOf_residualCharacter_stabilizer
  have hp : (p : 𝓞 (realCyclotomicField p)) ∈ (realPrimeAboveConductor p).asIdeal := by
    change (p : 𝓞 (realCyclotomicField p)) ∈ RingHom.ker (realCyclotomicReduction p)
    simp
  simpa only [map_natCast] using
    (Ideal.mem_of_liesOver Q (realPrimeAboveConductor p).asIdeal
      (p : 𝓞 (realCyclotomicField p))).mp hp

end HilbertModularity.Cyclotomic
