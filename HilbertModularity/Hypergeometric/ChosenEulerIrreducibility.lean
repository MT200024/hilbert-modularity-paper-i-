/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.GaloisRealizationCompatibleSystem
public import HilbertModularity.Hypergeometric.GaloisRealizationGenericMonodromy
public import HilbertModularity.RepresentationTheory.CharacterTwist
public import HilbertModularity.RepresentationTheory.DualIrreducibility
public import HilbertModularity.RepresentationTheory.Duality
public import HilbertModularity.RepresentationTheory.Irreducibility

/-! # Irreducibility of the chosen prime-level Euler realization

The source irreducibility is over the specified finite cyclotomic coefficient
completion. Absolute irreducibility is a separate manuscript deduction using
the exact determinant and a real-place involution.
-/

public noncomputable section

open AlgebraicGeometry IsDedekindDomain
open scoped NumberField

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic

local instance chosenEulerIrreducibilityCompletionNorm (p : ℕ) [Fact p.Prime]
    (w : HeightOneSpectrum (𝓞 (cyclotomicField p))) :
    NontriviallyNormedField (w.adicCompletion (cyclotomicField p)) :=
  Valued.toNontriviallyNormedField (w.adicCompletion (cyclotomicField p))
    (WithZero (Multiplicative ℤ))

/-- **Named literature input.** The symmetric parameters
`(m/N, 1-m/N); (1,1)` are generic for `0<m<N`, with integral upper
and lower sums `1` and `2`. [GPRV, Theorem 10.1, pp.45–46] gives
irreducibility at every nonsingular real-field specialization and every
finite cyclotomic coefficient completion, for all coprime conductors.
The chosen quotient component is the same primitive realization by
[GPRV, Theorem 9.2 and Proposition 9.5, pp.40–41]. The finite κ twist
preserves invariant subspaces, so the raw component has the same
irreducibility. No arbitrary scalar-extension irreducibility is asserted.

This generalizes the former conductor-prime input, whose old public
statement below is a proved specialization. The cited source remains
admitted once; no manuscript comparison or modularity is an input. -/
theorem commonEulerCompletionAction_isIrreducible_of_coprime
    (N m : ℕ) [NeZero N]
    (h3 : 3 ≤ N) (hm : 0 < m) (hmN : m < N) (hcop : m.Coprime N)
    (𝒞 : SmoothProperEulerFamily N m)
    (R : CommonRealEulerQuotientRealization N m 𝒞)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    (w : HeightOneSpectrum (𝓞 (cyclotomicField N))) :
    (commonEulerCompletionAction N m 𝒞 R ξ w).IsIrreducible := by
  sorry

/-- The conductor-prime specialization of the single all-coprime GPRV
irreducibility input. The original quotient and coefficient place are retained. -/
theorem chosenEulerConductorCompletion_isIrreducible
    (p m : ℕ) [NeZero p] [Fact p.Prime]
    (hN : p.Prime) (h5 : 5 ≤ p) (hm : 0 < m) (hmN : m < p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (w : HeightOneSpectrum (𝓞 (cyclotomicField p)))
    [w.asIdeal.LiesOver (Ideal.span {(p : ℤ)})] :
    let 𝒞 := chosenSmoothProperEulerFamily p m hN h5 hm hmN
    let R := chosenCommonRealEulerQuotientRealization p m 𝒞 hN h5 hm hmN
    (commonEulerCompletionAction p m 𝒞 R ξ w).IsIrreducible := by
  exact commonEulerCompletionAction_isIrreducible_of_coprime
    p m (le_trans (by decide) h5) hm hmN
    (hN.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hm hmN)).symm
    (chosenSmoothProperEulerFamily p m hN h5 hm hmN)
    (chosenCommonRealEulerQuotientRealization p m
      (chosenSmoothProperEulerFamily p m hN h5 hm hmN) hN h5 hm hmN) ξ w

/-- The manuscript's split-involution argument upgrades source-field
irreducibility of the *chosen* Euler action to irreducibility over any
coefficient extension. Its odd determinant remains an explicit application
input; it is not attributed to [GPRV, Theorem 10.1]. -/
theorem chosenEulerConductorCompletion_absoluteIrreducible_of_odd
    (p m : ℕ) [NeZero p] [Fact p.Prime]
    (hN : p.Prime) (h5 : 5 ≤ p) (hm : 0 < m) (hmN : m < p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (w : HeightOneSpectrum (𝓞 (cyclotomicField p)))
    [w.asIdeal.LiesOver (Ideal.span {(p : ℤ)})]
    (c : HilbertModularForms.AbsoluteGalois (realCyclotomicField p))
    (hc : c ^ 2 = 1)
    (hdet : let 𝒞 := chosenSmoothProperEulerFamily p m hN h5 hm hmN
      let R := chosenCommonRealEulerQuotientRealization p m 𝒞 hN h5 hm hmN
      LinearMap.det (commonEulerCompletionAction p m 𝒞 R ξ w c) = -1)
    (M : Type*) [Field M]
    [Algebra (w.adicCompletion (cyclotomicField p)) M] :
    let 𝒞 := chosenSmoothProperEulerFamily p m hN h5 hm hmN
    let R := chosenCommonRealEulerQuotientRealization p m 𝒞 hN h5 hm hmN
    ((commonEulerCompletionAction p m 𝒞 R ξ w).baseChange M).IsIrreducible := by
  let 𝒞 := chosenSmoothProperEulerFamily p m hN h5 hm hmN
  let R := chosenCommonRealEulerQuotientRealization p m 𝒞 hN h5 hm hmN
  let ρ := commonEulerCompletionAction p m 𝒞 R ξ w
  let : ρ.IsIrreducible :=
    chosenEulerConductorCompletion_isIrreducible p m hN h5 hm hmN ξ w
  have htwoFp : (2 : cyclotomicField p) ≠ 0 := by
    exact (map_ne_zero (cyclotomicField p).val).mp (by norm_num)
  have htwo : (2 : w.adicCompletion (cyclotomicField p)) ≠ 0 := by
    simpa only [map_ofNat] using
      (map_ne_zero (algebraMap (cyclotomicField p)
        (w.adicCompletion (cyclotomicField p)))).mpr htwoFp
  exact Representation.isIrreducible_baseChange_of_involution ρ
    htwo c hc hdet

end HilbertModularity.Hypergeometric



namespace Representation

variable {K G V W : Type*} [Field K] [Group G]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- Irreducibility transports across an equivariant linear equivalence. -/
theorem isIrreducible_equiv {ρ : Representation K G V}
    {σ : Representation K G W} (e : ρ.Equiv σ)
    (hρ : ρ.IsIrreducible) : σ.IsIrreducible :=
  (OrderIso.isSimpleOrder_iff e.subrepresentationOrderIso).mp hρ

/-- A character-twisted cohomological dual is irreducible exactly when its
covariant source is, in the direction needed for the selected Euler comparison. -/
theorem isIrreducible_of_characterTensorDualEquiv
    (ρ : Representation K G V) (σ : Representation K G W)
    [FiniteDimensional K W] (χ : G →* Kˣ)
    (e : ((Representation.ofCharacter χ).tprod σ.dual).Equiv ρ)
    (hρ : ρ.IsIrreducible) : σ.IsIrreducible := by
  have htw : ((Representation.ofCharacter χ).tprod σ.dual).IsIrreducible :=
    isIrreducible_equiv e.symm hρ
  have hdual : σ.dual.IsIrreducible :=
    (OrderIso.isSimpleOrder_iff
      (characterTensorSubrepresentationEquiv σ.dual χ)).mpr htw
  have hbidual : σ.dual.dual.IsIrreducible := by
    let : σ.dual.IsIrreducible := hdual
    exact isIrreducible_dual σ.dual
  exact isIrreducible_equiv (HilbertModularity.representationBidualEquiv σ).symm hbidual

/-- At an involution, a rank-two character twist of the dual has the same
odd determinant as the covariant action. The character value squares to one
because the involution does. -/
theorem det_eq_neg_one_of_characterTensorDualEquiv
    (ρ σ : Representation K G (Fin 2 → K)) (χ : G →* Kˣ)
    (e : ((Representation.ofCharacter χ).tprod σ.dual).Equiv ρ)
    (c : G) (hc : c ^ 2 = 1)
    (hσ : LinearMap.det (σ c) = -1) :
    LinearMap.det (ρ c) = -1 := by
  let et : (σ.dual.characterTwist χ).Equiv ρ :=
    (σ.dual.characterTwistTensorEquiv χ).symm.trans e
  have hcc : c * c = 1 := by simpa only [pow_two] using hc
  have hcinv : c⁻¹ = c := by
    calc
      c⁻¹ = c⁻¹ * 1 := by simp
      _ = c⁻¹ * (c * c) := by rw [hcc]
      _ = c := by group
  have hchi : (χ c : K) ^ 2 = 1 := by
    have h : χ c ^ 2 = (1 : Kˣ) := by rw [← map_pow, hc, map_one]
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
      congrArg (fun u : Kˣ => (u : K)) h
  have hdual : LinearMap.det (σ.dual c) = -1 := by
    change LinearMap.det ((σ c⁻¹).dualMap) = -1
    rw [hcinv, LinearMap.det_dualMap, hσ]
  have hrank : Module.finrank K (Module.Dual K (Fin 2 → K)) = 2 := by simp
  have htwist : LinearMap.det ((σ.dual.characterTwist χ) c) =
      (χ c : K) ^ 2 * LinearMap.det (σ.dual c) := by
    change LinearMap.det ((χ c : K) • σ.dual c) = _
    simp only [LinearMap.det_smul, hrank]
  calc
    LinearMap.det (ρ c) = LinearMap.det ((σ.dual.characterTwist χ) c) :=
      (et.determinant_eq c).symm
    _ = (χ c : K) ^ 2 * LinearMap.det (σ.dual c) := htwist
    _ = -1 := by rw [hchi, hdual, one_mul]

/-- The manuscript's odd-involution argument applies to both sides of a
character comparison, after the determinant is computed on the
covariant side. No source irreducibility is silently upgraded here. -/
theorem irreducible_pair_baseChange_of_characterTensorDualEquiv
    (ρ σ : Representation K G (Fin 2 → K)) (χ : G →* Kˣ)
    (e : ((Representation.ofCharacter χ).tprod σ.dual).Equiv ρ)
    (hρ : ρ.IsIrreducible) (h2 : (2 : K) ≠ 0)
    (c : G) (hc : c ^ 2 = 1)
    (hσdet : LinearMap.det (σ c) = -1)
    (M : Type*) [Field M] [Algebra K M] :
    (ρ.baseChange M).IsIrreducible ∧ (σ.baseChange M).IsIrreducible := by
  let : ρ.IsIrreducible := hρ
  let : σ.IsIrreducible :=
    isIrreducible_of_characterTensorDualEquiv ρ σ χ e hρ
  have hρdet : LinearMap.det (ρ c) = -1 :=
    det_eq_neg_one_of_characterTensorDualEquiv ρ σ χ e c hc hσdet
  exact ⟨isIrreducible_baseChange_of_involution ρ h2 c hc hρdet,
    isIrreducible_baseChange_of_involution σ h2 c hc hσdet⟩

end Representation

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic HilbertModularForms

/-- The already constructed finite character comparing the *same* chosen
Euler descent with Darmon's fixed labelled cohomological family transports
coefficient-field irreducibility to its covariant labelled Tate factor. The
Euler irreducibility premise is kept at this exact coefficient field; it is
not silently carried through an arbitrary scalar extension. -/
theorem darmonLabelledTate_isIrreducible_of_selectedEuler
    (N m : ℕ) [NeZero N] [Fact N.Prime]
    (hN : N.Prime) (h5 : 5 ≤ N) (hmPos : 0 < m) (hmN : m < N)
    (E : IntermediateField ℚ Qbar) [NumberField E]
    (hE : IntermediateField.normalClosure ℚ (realCyclotomicField N) Qbar ≤ E)
    (w : HeightOneSpectrum (𝓞 E))
    [w.asIdeal.LiesOver (Ideal.span {(N : ℤ)})]
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra (w.adicCompletion E) L]
    [ContinuousSMul (w.adicCompletion E) L]
    [NormedAlgebra ℚ_[N] L] [FiniteDimensional ℚ_[N] L]
    [IsScalarTower ℚ_[N] (w.adicCompletion E) L]
    [Algebra ℚ L] [IsScalarTower ℚ (w.adicCompletion E) L]
    [IsScalarTower ℚ ℚ_[N] L]
    (𝒞 : SmoothProperEulerFamily N m)
    (R : CommonRealEulerQuotientRealization N m 𝒞)
    (ι : cyclotomicField N →+* L)
    (hι : coefficientEmbeddingAbovePrime N m
        (eulerExponent_coprime_of_prime N m hN hmPos hmN) E
        ((IntermediateField.le_normalClosure (realCyclotomicField N)).trans hE)
        w L (tau N 1) =
      ι ((root N) ^ m + (root N)⁻¹ ^ m))
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    (ρ : Representation L (AbsoluteGalois (realCyclotomicField N)) (Fin 2 → L))
    (e : ρ.Equiv (puncturedFiberArithmeticRepresentation (realCyclotomicField N) ξ
      (darmonLabelledTateFamily (realCyclotomicField N)
        N (le_trans (by decide : 3 ≤ 5) h5) N m
        (eulerExponent_coprime_of_prime N m hN hmPos hmN) E hE w L)))
    (hEuler : let D := R.placeDescent N m 𝒞 N L ι
      (puncturedFiberArithmeticRepresentation (realCyclotomicField N) ξ
        D.localSystem).IsIrreducible) :
    ρ.IsIrreducible := by
  let D := R.placeDescent N m 𝒞 N L ι
  obtain ⟨ν, _hν, hνfin, χ, _hχ, _hcoeff, hcomparison⟩ :=
    exists_algebraic_character_comparing_selectedEuler_realization
      N m hN h5 hmPos hmN E hE w L 𝒞 R ι hι ξ
  let : Algebra E L := ((algebraMap (w.adicCompletion E) L).comp
    (algebraMap E (w.adicCompletion E))).toAlgebra
  let E' := RepresentationTheory.finiteCharacterCoefficientField (E₀ := E) ν
  let : NumberField E' :=
    RepresentationTheory.numberField_finiteCharacterCoefficientField ν hνfin
  have eDual : ρ.dual.Equiv
      (puncturedFiberArithmeticRepresentation (realCyclotomicField N) ξ
        (darmonCohomologicalFamily (realCyclotomicField N)
          N (le_trans (by decide : 3 ≤ 5) h5) N m
          (eulerExponent_coprime_of_prime N m hN hmPos hmN) E hE w L)) := by
    unfold puncturedFiberArithmeticRepresentation darmonCohomologicalFamily
    rw [Scheme.EtaleLocalSystem.cohDual_arithmeticRepresentation]
    exact HilbertModularity.representationDualEquiv e
  obtain ⟨ec⟩ := hcomparison ξ
  let et := Representation.characterTensorEquivCongr
    ((Units.map E'.subtype.toMonoidHom).comp χ.toMonoidHom) eDual
  exact Representation.isIrreducible_of_characterTensorDualEquiv
    _ ρ _ (et.trans ec) hEuler

end HilbertModularity.Hypergeometric

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic HilbertModularForms

/-- The coefficient completion's native valued field structure. -/
local instance chosenEulerComparisonCompletionNorm (p : ℕ) [Fact p.Prime]
    (w : HeightOneSpectrum (𝓞 (cyclotomicField p))) :
    NontriviallyNormedField (w.adicCompletion (cyclotomicField p)) :=
  Valued.toNontriviallyNormedField (w.adicCompletion (cyclotomicField p))
    (WithZero (Multiplicative ℤ))

/-- The actual chosen Euler action and a covariant rank-two action compared to
its cohomological dual by one character are absolutely irreducible
after an odd determinant calculation on the covariant side. The character
comparison and determinant remain explicit here so a same-family consumer
can supply them without admitting an irreducibility conclusion. -/
theorem chosenEulerConductor_absoluteIrreducible_of_comparison
    (p m : ℕ) [NeZero p] [Fact p.Prime]
    (hN : p.Prime) (h5 : 5 ≤ p) (hm : 0 < m) (hmN : m < p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (w : HeightOneSpectrum (𝓞 (cyclotomicField p)))
    [w.asIdeal.LiesOver (Ideal.span {(p : ℤ)})]
    (σ : Representation (w.adicCompletion (cyclotomicField p))
      (AbsoluteGalois (realCyclotomicField p))
      (Fin 2 → w.adicCompletion (cyclotomicField p)))
    (χ : AbsoluteGalois (realCyclotomicField p) →*
      (w.adicCompletion (cyclotomicField p))ˣ)
    (e : let 𝒞 := chosenSmoothProperEulerFamily p m hN h5 hm hmN
      let R := chosenCommonRealEulerQuotientRealization p m 𝒞 hN h5 hm hmN
      ((Representation.ofCharacter χ).tprod σ.dual).Equiv
        (commonEulerCompletionAction p m 𝒞 R ξ w))
    (c : AbsoluteGalois (realCyclotomicField p)) (hc : c ^ 2 = 1)
    (hσdet : LinearMap.det (σ c) = -1)
    (M : Type*) [Field M]
    [Algebra (w.adicCompletion (cyclotomicField p)) M] :
    let 𝒞 := chosenSmoothProperEulerFamily p m hN h5 hm hmN
    let R := chosenCommonRealEulerQuotientRealization p m 𝒞 hN h5 hm hmN
    ((commonEulerCompletionAction p m 𝒞 R ξ w).baseChange M).IsIrreducible ∧
      (σ.baseChange M).IsIrreducible := by
  let 𝒞 := chosenSmoothProperEulerFamily p m hN h5 hm hmN
  let R := chosenCommonRealEulerQuotientRealization p m 𝒞 hN h5 hm hmN
  let ρ := commonEulerCompletionAction p m 𝒞 R ξ w
  have hρ : ρ.IsIrreducible :=
    chosenEulerConductorCompletion_isIrreducible p m hN h5 hm hmN ξ w
  have htwoFp : (2 : cyclotomicField p) ≠ 0 := by
    exact (map_ne_zero (cyclotomicField p).val).mp (by norm_num)
  have htwo : (2 : w.adicCompletion (cyclotomicField p)) ≠ 0 := by
    simpa only [map_ofNat] using
      (map_ne_zero (algebraMap (cyclotomicField p)
        (w.adicCompletion (cyclotomicField p)))).mpr htwoFp
  exact Representation.irreducible_pair_baseChange_of_characterTensorDualEquiv
    ρ σ χ e hρ htwo c hc hσdet M

end HilbertModularity.Hypergeometric
