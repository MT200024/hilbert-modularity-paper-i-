/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.ComparisonCharacterWeights
public import HilbertModularity.Hypergeometric.RMComparison

/-! # Finite generic comparison from the weights at one arithmetic section

Geometric Schur descent constructs the character once on the arithmetic
quotient. Its specialization at one section has finite image by the labelled
weights of both representations. This is the finiteness step of
[TripathiGoswamiRevised, Theorem `thm:RMgeneral`, steps 3–5], without an
exact determinant normalization for either family.
-/

public noncomputable section

open NumberField IsDedekindDomain NumberField.LocalGalois
attribute [local instance] completionPadicAlgebra completionPadicTower
  completionComplexAlgebra completionComplexTower completionComplexRationalTower

namespace HilbertModularity.Hypergeometric

/-- A geometric comparison and the weights at one arithmetic section produce
one finite character, valid along every section whose projection is conjugate
to the identity. No finite-character or exact-determinant premise is used. -/
theorem exists_uniform_finite_comparison_character_of_weights_zero_one
    (p : ℕ) [Fact p.Prime]
    {F E₀ L G : Type} [Field F] [NumberField F] [Field E₀] [NumberField E₀]
    [NontriviallyNormedField L] [CompleteSpace L]
    [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
    [Group G] [TopologicalSpace G] [ContinuousInv G] [CompactSpace G]
    (ι₀ : E₀ →+* L)
    (π : G →* HilbertModularForms.AbsoluteGalois F)
    (hπ : Function.Surjective π) (hπc : Continuous π)
    (s : HilbertModularForms.AbsoluteGalois F →* G)
    (hsc : Continuous s) (hs : ∀ g, π (s g) = g)
    (n0 n1 : ℕ) (hn0 : n0 = 2) (hn1 : n1 = 2)
    (ρ0 : Representation L G (Fin n0 → L))
    (ρ1 : Representation L G (Fin n1 → L))
    (h0 : Continuous fun gv : G × (Fin n0 → L) => ρ0 gv.1 gv.2)
    (h1 : Continuous fun gv : G × (Fin n1 → L) => ρ1 gv.1 gv.2)
    (eGeom : Representation.Equiv (ρ0.comp π.ker.subtype) (ρ1.comp π.ker.subtype))
    [Representation.IsIrreducible
      (Representation.baseChange (AlgebraicClosure L) (ρ0.comp π.ker.subtype))]
    (bad0 bad1 : Finset (HeightOneSpectrum (𝓞 F)))
    (hunram0 : ∀ (q : HeightOneSpectrum (𝓞 F)) (Q : Ideal (𝓞 (AlgebraicClosure F))),
      Q.IsMaximal → Q.LiesOver q.asIdeal → ∀ g : HilbertModularForms.AbsoluteGalois F,
      g ∈ Q.inertia (HilbertModularForms.AbsoluteGalois F) → q ∉ bad0 →
        ρ0 (s g) = 1)
    (hunram1 : ∀ (q : HeightOneSpectrum (𝓞 F)) (Q : Ideal (𝓞 (AlgebraicClosure F))),
      Q.IsMaximal → Q.LiesOver q.asIdeal → ∀ g : HilbertModularForms.AbsoluteGalois F,
      g ∈ Q.inertia (HilbertModularForms.AbsoluteGalois F) → q ∉ bad1 →
        ρ1 (s g) = 1)
    (hHT0 : ∀ (q : HeightOneSpectrum (𝓞 F))
      [q.asIdeal.LiesOver (Ideal.span {(p : ℤ)})],
      Function.Bijective (HodgeTate.comparison p (AlgEquiv.restrictScalarsHom ℚ_[p])
        (PadicComplex.localGalois_fixes_base p (K := q.adicCompletion F))
        (Representation.restrictScalars ℚ_[p] ((ρ0.comp s).comp (localGaloisRestriction p F q)))))
    (hmult0 : ∀ (q : HeightOneSpectrum (𝓞 F))
      [q.asIdeal.LiesOver (Ideal.span {(p : ℤ)})],
      ∀ (τ : q.adicCompletion F →ₐ[ℚ_[p]] AlgebraicClosure L) (n : ℤ),
      Module.finrank (AlgebraicClosure L) (HodgeTate.labelledWeightSpace p
        (AlgEquiv.restrictScalarsHom ℚ_[p])
        (PadicComplex.localGalois_fixes_base p (K := q.adicCompletion F))
        ((ρ0.comp s).comp (localGaloisRestriction p F q)) n τ) =
          (if n = 0 then 1 else 0) + (if n = 1 then 1 else 0))
    (hHT1 : ∀ (q : HeightOneSpectrum (𝓞 F))
      [q.asIdeal.LiesOver (Ideal.span {(p : ℤ)})],
      Function.Bijective (HodgeTate.comparison p (AlgEquiv.restrictScalarsHom ℚ_[p])
        (PadicComplex.localGalois_fixes_base p (K := q.adicCompletion F))
        (Representation.restrictScalars ℚ_[p] ((ρ1.comp s).comp (localGaloisRestriction p F q)))))
    (hmult1 : ∀ (q : HeightOneSpectrum (𝓞 F))
      [q.asIdeal.LiesOver (Ideal.span {(p : ℤ)})],
      ∀ (τ : q.adicCompletion F →ₐ[ℚ_[p]] AlgebraicClosure L) (n : ℤ),
      Module.finrank (AlgebraicClosure L) (HodgeTate.labelledWeightSpace p
        (AlgEquiv.restrictScalarsHom ℚ_[p])
        (PadicComplex.localGalois_fixes_base p (K := q.adicCompletion F))
        ((ρ1.comp s).comp (localGaloisRestriction p F q)) n τ) =
          (if n = 0 then 1 else 0) + (if n = 1 then 1 else 0)) :
    ∃ ν : HilbertModularForms.AbsoluteGalois F →* Lˣ,
      Continuous ν ∧ (Set.range ν).Finite ∧
      Nonempty (((Representation.ofCharacter (ν.comp π)).tprod ρ0).Equiv ρ1) ∧
      ∀ (t : HilbertModularForms.AbsoluteGalois F →* G)
        (a : HilbertModularForms.AbsoluteGalois F),
        (∀ g, π (t g) = a * g * a⁻¹) →
        Nonempty (((Representation.ofCharacter ν).tprod (ρ0.comp t)).Equiv
          (ρ1.comp t)) := by
  subst n0
  subst n1
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ_[p] L).injective
  obtain ⟨ν, hνc, e, hsections⟩ :=
    Representation.exists_uniform_comparison_character π hπ hπc ρ0 ρ1
      (fun v => h0.comp (continuous_id.prodMk continuous_const))
      (fun v => h1.comp (continuous_id.prodMk continuous_const))
      eGeom (AlgebraicClosure L)
  have es := hsections s 1 (fun g => by simpa using hs g)
  have hfinite := finite_range_comparisonCharacter_of_weights_zero_one p ι₀
    (ρ0.comp s) (ρ1.comp s)
    (h0.comp ((hsc.comp continuous_fst).prodMk continuous_snd))
    (h1.comp ((hsc.comp continuous_fst).prodMk continuous_snd))
    ν es.some bad0 bad1 hunram0 hunram1 hHT0 hmult0 hHT1 hmult1
  exact ⟨ν, hνc, hfinite, e, hsections⟩

end HilbertModularity.Hypergeometric
