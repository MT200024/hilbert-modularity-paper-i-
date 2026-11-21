/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.HodgeTateDeterminant
public import HilbertModularity.RepresentationTheory.LabelledCharacterAlgebraization
public import HilbertModularity.NumberTheory.CyclotomicLocalCharacter

/-! # Finite normalized determinants from weights zero and one

This proves the determinant deduction of [TripathiGoswamiRevised,
Proposition 2.5] for an actual global representation. The input weights are
those of the original rank-two representation at the actual completions.
-/

public noncomputable section

open NumberField IsDedekindDomain NumberField.LocalGalois

attribute [local instance] completionPadicAlgebra completionPadicTower
  completionComplexAlgebra completionComplexTower completionComplexRationalTower

namespace HilbertModularity

variable (p : ℕ) [Fact p.Prime]
  {F E₀ L V : Type} [Field F] [NumberField F] [Field E₀] [NumberField E₀]
  [NontriviallyNormedField L] [CompleteSpace L]
  [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
  [AddCommGroup V] [Module L V] [Module ℚ_[p] V] [IsScalarTower ℚ_[p] L V]
  [FiniteDimensional L V] [FiniteDimensional ℚ_[p] V]
  [TopologicalSpace V] [T2Space V] [IsTopologicalAddGroup V] [ContinuousSMul L V]
  [IsModuleTopology ℚ_[p] V] [IsModuleTopology L V]

omit [T2Space V] [IsTopologicalAddGroup V] [ContinuousSMul L V]
  [IsModuleTopology L V] [CompleteSpace L] [FiniteDimensional ℚ_[p] L]
  [Module ℚ_[p] V] [IsScalarTower ℚ_[p] L V] [FiniteDimensional L V]
  [FiniteDimensional ℚ_[p] V] [TopologicalSpace V]
  [IsModuleTopology ℚ_[p] V] in
/-- Restriction of the global normalized determinant equals the local one:
the determinant commutes with restriction, and the chosen embedding of the
global algebraic closure preserves the actual action on roots of unity. -/
theorem normalizedDeterminant_localGaloisRestriction
    (ρ : Representation L (HilbertModularForms.AbsoluteGalois F) V)
    (q : HeightOneSpectrum (𝓞 F)) [q.asIdeal.LiesOver (Ideal.span {(p : ℤ)})] :
    (ρ.determinantCharacter * (Field.cyclotomicCharacterWithCoefficients F p L).toMonoidHom).comp
      (localGaloisRestriction p F q) =
      HodgeTate.normalizedDeterminant p (q.adicCompletion F)
        (ρ.comp (localGaloisRestriction p F q)) := by
  let := globalPadicAlgebra p F q
  ext g
  rw [HodgeTate.normalizedDeterminant_apply]
  change (ρ.determinantCharacter (localGaloisRestriction p F q g) : L) *
      (Field.cyclotomicCharacterWithCoefficients F p L (localGaloisRestriction p F q g) : L) =
    (ρ.determinantCharacter (localGaloisRestriction p F q g) : L) *
      (Field.cyclotomicCharacterWithCoefficients ℚ_[p] p L
        (AlgEquiv.restrictScalarsHom ℚ_[p] g) : L)
  congr 1
  simp only [Field.cyclotomicCharacterWithCoefficients_coe]
  congr 2
  exact congrArg (fun u : ℤ_[p]ˣ => (u : ℤ_[p]))
    (cyclotomicCharacter.eq_of_equivariant_embedding p
      (algebraicClosureEmbedding p F q).toRingHom
      (localGaloisRestriction p F q g).toRingEquiv g.toRingEquiv
      (localGaloisRestriction_commutes p F q g))

omit [IsModuleTopology L V] in
/-- A continuous rank-two representation with labelled weights `{0,1}` has
finite normalized determinant, provided that determinant is finitely ramified.
Local Hodge–Tate comparison and multiplicities refer to the original
representation. Determinant compatibility, actual local restriction, and the
proved rank-one algebraization deduction supply the conclusion. No finite-order
determinant premise, purity premise, or manuscript-family identification is used. -/
theorem finite_order_normalizedDeterminant_of_weights_zero_one
    (ι₀ : E₀ →+* L)
    (ρ : Representation L (HilbertModularForms.AbsoluteGalois F) V)
    (hρ : Continuous fun gv : HilbertModularForms.AbsoluteGalois F × V => ρ gv.1 gv.2)
    (hd : Module.finrank L V = 2)
    (bad : Finset (HeightOneSpectrum (𝓞 F)))
    (hunram : ∀ (q : HeightOneSpectrum (𝓞 F)) (Q : Ideal (𝓞 (AlgebraicClosure F))),
      Q.IsMaximal → Q.LiesOver q.asIdeal → ∀ g : HilbertModularForms.AbsoluteGalois F,
      g ∈ Q.inertia (HilbertModularForms.AbsoluteGalois F) → q ∉ bad →
        (ρ.determinantCharacter *
          (Field.cyclotomicCharacterWithCoefficients F p L).toMonoidHom) g = 1)
    (hHT : ∀ (q : HeightOneSpectrum (𝓞 F))
      [q.asIdeal.LiesOver (Ideal.span {(p : ℤ)})],
      Function.Bijective (HodgeTate.comparison p (AlgEquiv.restrictScalarsHom ℚ_[p])
        (PadicComplex.localGalois_fixes_base p (K := q.adicCompletion F))
        (Representation.restrictScalars ℚ_[p] (ρ.comp (localGaloisRestriction p F q)))))
    (hmult : ∀ (q : HeightOneSpectrum (𝓞 F))
      [q.asIdeal.LiesOver (Ideal.span {(p : ℤ)})],
      ∀ (τ : q.adicCompletion F →ₐ[ℚ_[p]] AlgebraicClosure L) (n : ℤ),
      Module.finrank (AlgebraicClosure L) (HodgeTate.labelledWeightSpace p
        (AlgEquiv.restrictScalarsHom ℚ_[p])
        (PadicComplex.localGalois_fixes_base p (K := q.adicCompletion F))
        (ρ.comp (localGaloisRestriction p F q)) n τ) =
          (if n = 0 then 1 else 0) + (if n = 1 then 1 else 0)) :
    ∃ n : ℕ, 0 < n ∧ ∀ g,
      ((ρ.determinantCharacter *
        (Field.cyclotomicCharacterWithCoefficients F p L).toMonoidHom) g) ^ n = 1 := by
  have hc : Continuous ρ.determinantCharacter :=
    Representation.continuous_determinantCharacter_of_basis (Module.finBasis L V)
      (fun i => ((Module.finBasis L V).coord i).continuous_of_finiteDimensional) ρ
      (fun v => hρ.comp (continuous_id.prodMk continuous_const))
  have hlocal (q : HeightOneSpectrum (𝓞 F))
      [q.asIdeal.LiesOver (Ideal.span {(p : ℤ)})] :=
    HodgeTate.normalizedDeterminant_weights_zero_of_weights_zero_one p (q.adicCompletion F)
      (ρ.comp (localGaloisRestriction p F q))
      (hρ.comp ((continuous_localGaloisRestriction p F q).comp continuous_fst |>.prodMk
        continuous_snd)) hd (hHT q) (hmult q)
  apply finite_order_of_labelledHodgeTate p ι₀ _
    (hc.mul (Field.cyclotomicCharacterWithCoefficients F p L).continuous) bad hunram
  · intro q hq
    rw [normalizedDeterminant_localGaloisRestriction p ρ q]
    exact (hlocal q).1
  · intro q hq
    rw [normalizedDeterminant_localGaloisRestriction p ρ q]
    exact (hlocal q).2

end HilbertModularity
