/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.RMComparisonDeterminant
public import HilbertModularity.RepresentationTheory.HodgeTateDeterminantAlgebraization
public import HilbertModularity.NumberTheory.ResidualRigidity

/-! # Finiteness from the Hodge weights of both compared representations

The same normalizing character cancels in the determinant ratio. Thus finite
normalized determinants on both sides suffice; no exact determinant identity
for one chosen family is required. This proves the determinant deduction in
[TripathiGoswamiRevised, Proposition 2.5 and Theorem `thm:RMgeneral`].
-/

public noncomputable section

namespace HilbertModularity.Hypergeometric

/-- Positive finite exponents for both normalized determinants force the
rank-two comparison character to have finite image. -/
theorem comparisonCharacter_finite_range_of_two_normalized_powers
    {G L V W : Type*} [Group G] [Field L]
    [AddCommGroup V] [Module L V] [AddCommGroup W] [Module L W]
    (ρ₀ : Representation L G V) (ρ₁ : Representation L G W)
    (ν ε : G →* Lˣ)
    (e : ((Representation.ofCharacter ν).tprod ρ₀).Equiv ρ₁)
    (hdim : Module.finrank L V = 2)
    (n₀ n₁ : ℕ) (hn₀ : 0 < n₀) (hn₁ : 0 < n₁)
    (h₀ : ∀ g, (ρ₀.determinantCharacter g * ε g) ^ n₀ = 1)
    (h₁ : ∀ g, (ρ₁.determinantCharacter g * ε g) ^ n₁ = 1) :
    (Set.range ν).Finite := by
  apply comparisonCharacter_finite_range_of_tensor_equiv_and_power
    ρ₀ ρ₁ ν ρ₀.determinantCharacter⁻¹ e hdim
    (fun g => mul_inv_cancel _) (n₀ * n₁) (Nat.mul_pos hn₀ hn₁)
  intro g
  have hratio : ρ₁.determinantCharacter g * ρ₀.determinantCharacter⁻¹ g =
      (ρ₁.determinantCharacter g * ε g) / (ρ₀.determinantCharacter g * ε g) := by
    change ρ₁.determinantCharacter g * (ρ₀.determinantCharacter g)⁻¹ = _
    simp [div_eq_mul_inv, mul_inv_rev, mul_assoc]
  have hleft : (ρ₁.determinantCharacter g * ε g) ^ (n₀ * n₁) = 1 := by
    rw [Nat.mul_comm n₀ n₁, pow_mul, h₁ g, one_pow]
  have hright : (ρ₀.determinantCharacter g * ε g) ^ (n₀ * n₁) = 1 := by
    rw [pow_mul, h₀ g, one_pow]
  rw [hratio, div_pow, hleft, hright]
  simp

end HilbertModularity.Hypergeometric

open NumberField IsDedekindDomain NumberField.LocalGalois
attribute [local instance] completionPadicAlgebra completionPadicTower
  completionComplexAlgebra completionComplexTower completionComplexRationalTower

namespace HilbertModularity

/-- Finite ramification of an action implies finite ramification of its
cyclotomic-normalized determinant. Only primes above the coefficient
characteristic are added to the supplied exceptional set. -/
theorem normalizedDeterminant_unramifiedOutsideFinite
    (p : ℕ) [Fact p.Prime]
    {F L V : Type*} [Field F] [NumberField F]
    [NontriviallyNormedField L] [NormedAlgebra ℚ_[p] L]
    [AddCommGroup V] [Module L V]
    (ρ : Representation L (HilbertModularForms.AbsoluteGalois F) V)
    (bad : Finset (HeightOneSpectrum (𝓞 F)))
    (hunram : ∀ (q : HeightOneSpectrum (𝓞 F)) (Q : Ideal (𝓞 (AlgebraicClosure F))),
      Q.IsMaximal → Q.LiesOver q.asIdeal → ∀ g : HilbertModularForms.AbsoluteGalois F,
      g ∈ Q.inertia (HilbertModularForms.AbsoluteGalois F) → q ∉ bad → ρ g = 1) :
    ∃ bad' : Finset (HeightOneSpectrum (𝓞 F)),
      ∀ (q : HeightOneSpectrum (𝓞 F)) (Q : Ideal (𝓞 (AlgebraicClosure F))),
      Q.IsMaximal → Q.LiesOver q.asIdeal → ∀ g : HilbertModularForms.AbsoluteGalois F,
      g ∈ Q.inertia (HilbertModularForms.AbsoluteGalois F) → q ∉ bad' →
        (ρ.determinantCharacter *
          (Field.cyclotomicCharacterWithCoefficients F p L).toMonoidHom) g = 1 := by
  classical
  have hpfin : {q : HeightOneSpectrum (𝓞 F) | (p : 𝓞 F) ∈ q.asIdeal}.Finite := by
    apply HeightOneSpectrum.finite_primes_containing
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  refine ⟨bad ∪ hpfin.toFinset, ?_⟩
  intro q Q hQ hQq g hg hq
  let := hQ
  let := hQq
  have hbad : q ∉ bad := fun h => hq (Finset.mem_union_left _ h)
  have hpq : (p : 𝓞 F) ∉ q.asIdeal := by
    intro h
    exact hq (Finset.mem_union_right _ (hpfin.mem_toFinset.mpr h))
  have hpQ : (p : 𝓞 (AlgebraicClosure F)) ∉ Q := by
    intro h
    apply hpq
    apply (Ideal.mem_of_liesOver Q q.asIdeal (p : 𝓞 F)).mpr
    simpa only [map_natCast] using h
  have hdet : ρ.determinantCharacter g = 1 := by
    apply Units.ext
    simp [Representation.determinantCharacter_coe, hunram q Q hQ hQq g hg hbad]
  have hcyc := Field.cyclotomicCharacterWithCoefficients_eq_one_on_inertia
    F p L Q hpQ ⟨g, hg⟩
  change ρ.determinantCharacter g * Field.cyclotomicCharacterWithCoefficients F p L g = 1
  rw [hdet, hcyc, one_mul]

/-- Two cohomological rank-two representations with weights zero and one
have a finite comparison character. The Hodge comparisons are for the actual
representations at every local label. Finite ramification is required of the
actions themselves; finite orders of the normalized determinants are proved. -/
theorem finite_range_comparisonCharacter_of_weights_zero_one
    (p : ℕ) [Fact p.Prime]
    {F E₀ L : Type} [Field F] [NumberField F] [Field E₀] [NumberField E₀]
    [NontriviallyNormedField L] [CompleteSpace L]
    [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
    (ι₀ : E₀ →+* L)
    (ρ0 ρ1 : Representation L (HilbertModularForms.AbsoluteGalois F) (Fin 2 → L))
    (h0 : Continuous fun gv : HilbertModularForms.AbsoluteGalois F × (Fin 2 → L) =>
      ρ0 gv.1 gv.2)
    (h1 : Continuous fun gv : HilbertModularForms.AbsoluteGalois F × (Fin 2 → L) =>
      ρ1 gv.1 gv.2)
    (ν : HilbertModularForms.AbsoluteGalois F →* Lˣ)
    (e : ((Representation.ofCharacter ν).tprod ρ0).Equiv ρ1)
    (bad0 bad1 : Finset (HeightOneSpectrum (𝓞 F)))
    (hunram0 : ∀ (q : HeightOneSpectrum (𝓞 F)) (Q : Ideal (𝓞 (AlgebraicClosure F))),
      Q.IsMaximal → Q.LiesOver q.asIdeal → ∀ g : HilbertModularForms.AbsoluteGalois F,
      g ∈ Q.inertia (HilbertModularForms.AbsoluteGalois F) → q ∉ bad0 →
        ρ0 g = 1)
    (hunram1 : ∀ (q : HeightOneSpectrum (𝓞 F)) (Q : Ideal (𝓞 (AlgebraicClosure F))),
      Q.IsMaximal → Q.LiesOver q.asIdeal → ∀ g : HilbertModularForms.AbsoluteGalois F,
      g ∈ Q.inertia (HilbertModularForms.AbsoluteGalois F) → q ∉ bad1 →
        ρ1 g = 1)
    (hHT0 : ∀ (q : HeightOneSpectrum (𝓞 F))
      [q.asIdeal.LiesOver (Ideal.span {(p : ℤ)})],
      Function.Bijective (HodgeTate.comparison p (AlgEquiv.restrictScalarsHom ℚ_[p])
        (PadicComplex.localGalois_fixes_base p (K := q.adicCompletion F))
        (Representation.restrictScalars ℚ_[p] (ρ0.comp (localGaloisRestriction p F q)))))
    (hmult0 : ∀ (q : HeightOneSpectrum (𝓞 F))
      [q.asIdeal.LiesOver (Ideal.span {(p : ℤ)})],
      ∀ (τ : q.adicCompletion F →ₐ[ℚ_[p]] AlgebraicClosure L) (n : ℤ),
      Module.finrank (AlgebraicClosure L) (HodgeTate.labelledWeightSpace p
        (AlgEquiv.restrictScalarsHom ℚ_[p])
        (PadicComplex.localGalois_fixes_base p (K := q.adicCompletion F))
        (ρ0.comp (localGaloisRestriction p F q)) n τ) =
          (if n = 0 then 1 else 0) + (if n = 1 then 1 else 0))
    (hHT1 : ∀ (q : HeightOneSpectrum (𝓞 F))
      [q.asIdeal.LiesOver (Ideal.span {(p : ℤ)})],
      Function.Bijective (HodgeTate.comparison p (AlgEquiv.restrictScalarsHom ℚ_[p])
        (PadicComplex.localGalois_fixes_base p (K := q.adicCompletion F))
        (Representation.restrictScalars ℚ_[p] (ρ1.comp (localGaloisRestriction p F q)))))
    (hmult1 : ∀ (q : HeightOneSpectrum (𝓞 F))
      [q.asIdeal.LiesOver (Ideal.span {(p : ℤ)})],
      ∀ (τ : q.adicCompletion F →ₐ[ℚ_[p]] AlgebraicClosure L) (n : ℤ),
      Module.finrank (AlgebraicClosure L) (HodgeTate.labelledWeightSpace p
        (AlgEquiv.restrictScalarsHom ℚ_[p])
        (PadicComplex.localGalois_fixes_base p (K := q.adicCompletion F))
        (ρ1.comp (localGaloisRestriction p F q)) n τ) =
          (if n = 0 then 1 else 0) + (if n = 1 then 1 else 0)) :
    (Set.range ν).Finite := by
  let : IsModuleTopology ℚ_[p] (Fin 2 → L) := isModuleTopologyOfFiniteDimensional
  obtain ⟨bad0', hunram0'⟩ := normalizedDeterminant_unramifiedOutsideFinite p ρ0 bad0 hunram0
  obtain ⟨bad1', hunram1'⟩ := normalizedDeterminant_unramifiedOutsideFinite p ρ1 bad1 hunram1
  obtain ⟨n0, hn0, hpow0⟩ := finite_order_normalizedDeterminant_of_weights_zero_one
    p ι₀ ρ0 h0 (by simp) bad0' hunram0' hHT0 hmult0
  obtain ⟨n1, hn1, hpow1⟩ := finite_order_normalizedDeterminant_of_weights_zero_one
    p ι₀ ρ1 h1 (by simp) bad1' hunram1' hHT1 hmult1
  exact Hypergeometric.comparisonCharacter_finite_range_of_two_normalized_powers
    ρ0 ρ1 ν (Field.cyclotomicCharacterWithCoefficients F p L).toMonoidHom
    e (by simp) n0 n1 hn0 hn1 hpow0 hpow1

/-- The comparison character has one positive exponent on the whole Galois
group. In particular, no coefficient extension is needed for finite order. -/
theorem finite_order_comparisonCharacter_of_weights_zero_one
    (p : ℕ) [Fact p.Prime]
    {F E₀ L : Type} [Field F] [NumberField F] [Field E₀] [NumberField E₀]
    [NontriviallyNormedField L] [CompleteSpace L]
    [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
    (ι₀ : E₀ →+* L)
    (ρ0 ρ1 : Representation L (HilbertModularForms.AbsoluteGalois F) (Fin 2 → L))
    (h0 : Continuous fun gv : HilbertModularForms.AbsoluteGalois F × (Fin 2 → L) =>
      ρ0 gv.1 gv.2)
    (h1 : Continuous fun gv : HilbertModularForms.AbsoluteGalois F × (Fin 2 → L) =>
      ρ1 gv.1 gv.2)
    (ν : HilbertModularForms.AbsoluteGalois F →* Lˣ)
    (e : ((Representation.ofCharacter ν).tprod ρ0).Equiv ρ1)
    (bad0 bad1 : Finset (HeightOneSpectrum (𝓞 F)))
    (hunram0 : ∀ (q : HeightOneSpectrum (𝓞 F)) (Q : Ideal (𝓞 (AlgebraicClosure F))),
      Q.IsMaximal → Q.LiesOver q.asIdeal → ∀ g : HilbertModularForms.AbsoluteGalois F,
      g ∈ Q.inertia (HilbertModularForms.AbsoluteGalois F) → q ∉ bad0 →
        ρ0 g = 1)
    (hunram1 : ∀ (q : HeightOneSpectrum (𝓞 F)) (Q : Ideal (𝓞 (AlgebraicClosure F))),
      Q.IsMaximal → Q.LiesOver q.asIdeal → ∀ g : HilbertModularForms.AbsoluteGalois F,
      g ∈ Q.inertia (HilbertModularForms.AbsoluteGalois F) → q ∉ bad1 →
        ρ1 g = 1)
    (hHT0 : ∀ (q : HeightOneSpectrum (𝓞 F))
      [q.asIdeal.LiesOver (Ideal.span {(p : ℤ)})],
      Function.Bijective (HodgeTate.comparison p (AlgEquiv.restrictScalarsHom ℚ_[p])
        (PadicComplex.localGalois_fixes_base p (K := q.adicCompletion F))
        (Representation.restrictScalars ℚ_[p] (ρ0.comp (localGaloisRestriction p F q)))))
    (hmult0 : ∀ (q : HeightOneSpectrum (𝓞 F))
      [q.asIdeal.LiesOver (Ideal.span {(p : ℤ)})],
      ∀ (τ : q.adicCompletion F →ₐ[ℚ_[p]] AlgebraicClosure L) (n : ℤ),
      Module.finrank (AlgebraicClosure L) (HodgeTate.labelledWeightSpace p
        (AlgEquiv.restrictScalarsHom ℚ_[p])
        (PadicComplex.localGalois_fixes_base p (K := q.adicCompletion F))
        (ρ0.comp (localGaloisRestriction p F q)) n τ) =
          (if n = 0 then 1 else 0) + (if n = 1 then 1 else 0))
    (hHT1 : ∀ (q : HeightOneSpectrum (𝓞 F))
      [q.asIdeal.LiesOver (Ideal.span {(p : ℤ)})],
      Function.Bijective (HodgeTate.comparison p (AlgEquiv.restrictScalarsHom ℚ_[p])
        (PadicComplex.localGalois_fixes_base p (K := q.adicCompletion F))
        (Representation.restrictScalars ℚ_[p] (ρ1.comp (localGaloisRestriction p F q)))))
    (hmult1 : ∀ (q : HeightOneSpectrum (𝓞 F))
      [q.asIdeal.LiesOver (Ideal.span {(p : ℤ)})],
      ∀ (τ : q.adicCompletion F →ₐ[ℚ_[p]] AlgebraicClosure L) (n : ℤ),
      Module.finrank (AlgebraicClosure L) (HodgeTate.labelledWeightSpace p
        (AlgEquiv.restrictScalarsHom ℚ_[p])
        (PadicComplex.localGalois_fixes_base p (K := q.adicCompletion F))
        (ρ1.comp (localGaloisRestriction p F q)) n τ) =
          (if n = 0 then 1 else 0) + (if n = 1 then 1 else 0)) :
    ∃ n : ℕ, 0 < n ∧ ∀ g, ν g ^ n = 1 := by
  have hfin := finite_range_comparisonCharacter_of_weights_zero_one p ι₀ ρ0 ρ1 h0 h1
    ν e bad0 bad1 hunram0 hunram1 hHT0 hmult0 hHT1 hmult1
  let : Finite ν.range := hfin.to_subtype
  refine ⟨Nat.card ν.range, Nat.card_pos, ?_⟩
  intro g
  exact congrArg Subtype.val (show (ν.rangeRestrict g) ^ Nat.card ν.range = 1 from pow_card_eq_one')

end HilbertModularity
