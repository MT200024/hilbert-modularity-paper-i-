/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.PrimePlusOrdinaryResidualTransport
public import HilbertModularity.Hypergeometric.PrimePlusRaynaudLocalOrdinaryRow

/-! # One residual ordering at all primes above the conductor

Order the characters on the fixed local Galois group before choosing any
absolute prime. Conjugacy invariance of the global characters preserves this
choice under the actual decomposition-group comparisons.
-/

public noncomputable section

open AlgebraicGeometry NumberField ValuativeRel
open scoped NumberField ValuativeRel

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic HilbertModularForms IsNonarchimedeanLocalField

attribute [local instance] realFieldAlgebra realPrimePowerCompletionPadicAlgebra
  Ideal.Quotient.field

local instance uniformOrdinaryCharP (p : ℕ) [Fact p.Prime] :
    CharP (𝒪[RealPrimePowerCompletion p 0] ⧸ 𝓂[RealPrimePowerCompletion p 0]) p :=
  inferInstanceAs (CharP 𝓀[RealPrimePowerCompletion p 0] p)

local instance uniformOrdinaryLocalGalCompact (p : ℕ) [Fact p.Prime] :
    CompactSpace (Gal(PadicAlgCl p/RealPrimePowerCompletion p 0)) := by
  let : IsGalois (RealPrimePowerCompletion p 0) (PadicAlgCl p) :=
    IsGalois.tower_top_of_isGalois ℚ_[p] (RealPrimePowerCompletion p 0) (PadicAlgCl p)
  infer_instance

/-- A specified native ordinary quotient and the same-Jacobian native Tate
comparison give one ordering of the global residual datum that works at every
absolute prime above the conductor. No cubic-cusp hypothesis is used. -/
theorem exists_primePlus_uniformOrdinaryOrdering
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) (RealPrimePowerCompletion p 0)]
    (β : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[RealPrimePowerCompletion p 0])
    (C : PrimePlusNativeTateComparison p hp ξ (RealPrimePowerCompletion p 0) β)
    (hmap : C.localMap = AlgHom.id ℚ_[p] (RealPrimePowerCompletion p 0))
    (d : PrimePlusNormalizedOrdinaryData p hp ξ 1 (Nat.coprime_one_left _))
    (D : SkinnerWilesResidualData (primePlusTateFieldCoordinateAction p hp ξ β)) :
    ∃ D' : SkinnerWilesResidualData (primePlusTateFieldCoordinateAction p hp ξ β),
      (D' = D ∨ D' = D.swap) ∧
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p))))
        [Q.IsMaximal] [Q.LiesOver (realPrimeAboveConductor p).asIdeal],
        Nonempty (SkinnerWilesOrdinaryAt p
          (primePlusTateFieldCoordinateAction p hp ξ β) D' Q) := by
  let E := RealPrimePowerCompletion p 0
  let ρ := primePlusTateFieldCoordinateAction p hp ξ β
  let r := primePlusLocalGaloisRestriction p
  let η := d.coordinateRepresentation p hp ξ
  let b := primePlusRaynaudLabelOneLocalEquiv p hp ξ β C hmap d 1
  let := d.lattice_isLattice
  let χ₁ := integerCharacter E d.upperCharacter d.upper_continuous
  let χ₂ := Representation.determinantCharacter d.lattice.toRepresentation
  let red := Units.map (Ideal.Quotient.mk 𝓂[E]).toMonoidHom
  have hb (g : Gal(PadicAlgCl p/E)) (v : Fin 2 → E) :
      b (ρ (r g) v) = η g (b v) := by
    dsimp only [b]
    rw [primePlusRaynaudLabelOneLocalEquiv_eq_generic]
    exact conjugatedRepresentationCoordinateEquiv_intertwines ρ
      (primePlusLocalTateRepresentation p hp ξ).ρ r η
      (primePlusNativeComparisonLocalEquiv p hp ξ β C hmap)
      (primePlusLabelOneRaynaudCoordinateEquiv p hp ξ d)
      r (MonoidHom.id _) 1 (fun _ => by simp) g v
  have hentry (g : Gal(PadicAlgCl p/E)) (i j : Fin 2) :
      b (ρ (r g) (b.symm (Pi.single j 1))) i =
        LinearMap.toMatrix d.basis d.basis
          ((primePlusDecompositionScalarConjugate p hp ξ 1
            (Nat.coprime_one_left _)).ρ g) i j := by
    rw [hb, b.apply_symm_apply]
    dsimp [η, PrimePlusNormalizedOrdinaryData.coordinateRepresentation]
    simp only [LinearMap.toMatrix_apply]
    simp
  have hχ₂ (g : Gal(PadicAlgCl p/E)) : ((χ₂ g : 𝒪[E]) : E) =
      (d.lowerCharacter g : E) :=
    congrArg (fun χ : Gal(PadicAlgCl p/E) →* Eˣ => (χ g : E))
      (Representation.map_determinantCharacter_characterLattice d.lowerCharacter d.lattice)
  have h2 : (2 : 𝒪[E] ⧸ 𝓂[E]) ≠ 0 := by
    intro h
    have hd : p ∣ 2 := (CharP.cast_eq_zero_iff (𝒪[E] ⧸ 𝓂[E]) p 2).mp h
    have := Nat.le_of_dvd (by decide : 0 < 2) hd
    omega
  have horder := D.localCharacters_eq_or_swap r χ₁ χ₂ h2 b
    (fun g => by rw [hentry, d.upperTriangular]; rfl)
    (fun g => by rw [hentry, d.upperTriangular, hχ₂]; rfl)
  have make (D' : SkinnerWilesResidualData ρ)
      (h₁ : red.comp χ₁ = D'.chi₁.comp r)
      (h₂ : red.comp χ₂ = D'.chi₂.comp r)
      (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p))))
      [Q.IsMaximal] [Q.LiesOver (realPrimeAboveConductor p).asIdeal] :
      Nonempty (SkinnerWilesOrdinaryAt p ρ D' Q) := by
    obtain ⟨σ, δ, hδc, hδ, hI⟩ := exists_primePlusDecompositionEquiv p hp Q
    let e := primePlusRaynaudLabelOneLocalEquiv p hp ξ β C hmap d σ
    refine ⟨d.skinnerWilesOrdinaryAt_of_equiv p hp ξ 1
      (Nat.coprime_one_left _) ρ D' Q δ.toMonoidHom hδc e
      (primePlusRaynaudLabelOneLocalEquiv_intertwines p hp ξ β C hmap d Q σ
        δ.toMonoidHom hδ) ?_ ?_ (fun g hg => (hI g).mp hg)⟩
    · intro g
      have ht := congrArg (fun χ => χ (δ g)) h₁
      change (red.comp χ₁) (δ g) = D'.chi₁ (r (δ g)) at ht
      rw [show r (δ g) = σ * (g : AbsoluteGalois (realCyclotomicField p)) * σ⁻¹
        from hδ g] at ht
      dsimp only [red, χ₁, E] at ht
      simpa [map_mul, mul_comm, mul_left_comm, mul_assoc] using ht
    · intro g
      have ht := congrArg (fun χ => χ (δ g)) h₂
      change (red.comp χ₂) (δ g) = D'.chi₂ (r (δ g)) at ht
      rw [show r (δ g) = σ * (g : AbsoluteGalois (realCyclotomicField p)) * σ⁻¹
        from hδ g] at ht
      dsimp only [red, χ₂, E] at ht
      simpa [map_mul, mul_comm, mul_left_comm, mul_assoc] using ht
  rcases horder with h | h
  · exact ⟨D, Or.inl rfl, make D h.1 h.2⟩
  · refine ⟨D.swap, Or.inr rfl, make D.swap ?_ ?_⟩
    · simpa only [SkinnerWilesResidualData.swap_chi₁] using h.1
    · simpa only [SkinnerWilesResidualData.swap_chi₂] using h.2

end HilbertModularity.Hypergeometric
