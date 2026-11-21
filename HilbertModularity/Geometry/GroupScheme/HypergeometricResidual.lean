/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.HypergeometricDeterminant
public import HilbertModularity.Geometry.GroupScheme.HypergeometricTorsionRank
public import HilbertModularity.Geometry.GroupScheme.HypergeometricRanks
public import HilbertModularity.RepresentationTheory.Irreducibility
public import HilbertModularity.RepresentationTheory.CharacterTwist

/-! # Residual constituents of the chosen prime-conductor fibre

A nonzero fixed point and the exact determinant of the same chosen integral
Tate factor imply the covariant and cohomological-dual constituents.  The
fixed point and exact determinant remain explicit arithmetic inputs until
the chosen family is compared with the plus family of [DarmonRigid,
Theorem 2.6(2)] and [DarmonMestre, Section 4].  The deductions follow
[TripathiGoswamiRevised, Proposition `primeresidual`].
-/

public section
noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NumberField TensorProduct

namespace HilbertModularity.Hypergeometric

open HilbertModularity.Cyclotomic AlgebraicGeometry.GroupScheme

variable (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p)
  (ξ : ProjectiveLine.Parameter (realCyclotomicField p))

local notation "Fₚ" => realCyclotomicField p
local notation "Rₚ" => 𝓞 Fₚ
local notation "Pₚ" => Ideal.span {realPrimeGenerator p}
local notation "Sₚ" => AdicCompletion Pₚ Rₚ
local notation "kₚ" => Rₚ ⧸ Pₚ

/-- A rank-two irreducible representation with an odd involution remains
irreducible after arbitrary extension of its coefficient field.  The
involution eigenlines are defined over the original field, as in
[TripathiGoswamiRevised, Lemma `prime-absolute-irred`]. -/
theorem absoluteIrreducible_of_oddInvolution
    {K E G V : Type*} [Field K] [Field E] [Algebra K E] [Group G]
    [AddCommGroup V] [Module K V] [Module.Finite K V]
    (ρ : Representation K G V) [ρ.IsIrreducible]
    (hrank : Module.finrank K V = 2) (hK : (2 : K) ≠ 0)
    (c : G) (hc : c ^ 2 = 1) (hdet : LinearMap.det (ρ c) = -1) :
    (ρ.baseChange E).IsIrreducible := by
  let b₀ := Module.finBasisOfFinrankEq K V hrank
  let M := LinearMap.toMatrix b₀ b₀ (ρ c)
  have hM : M ^ 2 = 1 := by
    dsimp [M]
    rw [sq, ← LinearMap.toMatrix_mul, ← map_mul, ← sq, hc, map_one,
      LinearMap.toMatrix_one]
  have hd : M.det = -1 := by
    simpa only [M, LinearMap.det_toMatrix] using hdet
  obtain ⟨d, hd₀, hd₁⟩ := HilbertModularity.exists_basis_of_involution hK M hM hd
  have htransport (w : Fin 2 → K) :
      b₀.equivFun.symm (M.mulVec w) = ρ c (b₀.equivFun.symm w) := by
    apply b₀.equivFun.injective
    ext i
    simp [M, LinearMap.toMatrix, map_smul]
    fin_cases i <;> simp_all
  let b : Module.Basis (Fin 2) K V := d.map b₀.equivFun.symm
  apply Representation.isIrreducible_baseChange_of_involution_basis ρ hK b c
  · simpa [b] using (htransport (d 0)).symm.trans (congrArg b₀.equivFun.symm hd₀)
  · simpa [b] using (htransport (d 1)).symm.trans (congrArg b₀.equivFun.symm hd₁)

/-- Irreducibility of the chosen characteristic-zero RM Tate factor becomes
absolute after extension of coefficients when its exact cyclotomic determinant
is odd at an involution.  The irreducibility input is the coefficient-field
specialization of [GPRV, Theorem 10.1] after the still separate RM comparison;
the exact determinant is the conclusion of [TripathiGoswamiRevised,
Lemma `det-rigidity`]. -/
theorem darmonPrimeIntegralTate_absoluteIrreducible
    (L E : Type*) [Field L] [Algebra Sₚ L] [IsFractionRing Sₚ L]
    [Field E] [Algebra L E]
    (hL : (2 : L) ≠ 0)
    (hirr : letI := darmonPrimeIntegralTateModule p hp ξ
      ((darmonPrimeIntegralTateRepresentation p hp ξ).baseChange L).IsIrreducible)
    (c : AlgebraicClosure Fₚ ≃ₐ[Fₚ] AlgebraicClosure Fₚ) (hc : c ^ 2 = 1)
    (hodd : algebraMap Sₚ L
      (TateModule.coefficientPrimeRingEquiv p Rₚ Pₚ ((p - 1) / 2)
        (realPrimeRamification_pos p (by omega)) (span_realPrimeGenerator_pow p (by omega))
          (PadicInt.toAdicCompletion p Rₚ (Field.cyclotomicCharacter Fₚ p c : ℤ_[p]))) = -1)
    (hdet : ∀ g : AlgebraicClosure Fₚ ≃ₐ[Fₚ] AlgebraicClosure Fₚ,
      letI := darmonPrimeIntegralTateModule p hp ξ
      LinearMap.det ((darmonPrimeIntegralTateRepresentation p hp ξ).baseChange L g) =
        algebraMap Sₚ L
          (TateModule.coefficientPrimeRingEquiv p Rₚ Pₚ ((p - 1) / 2)
            (realPrimeRamification_pos p (by omega)) (span_realPrimeGenerator_pow p (by omega))
              (PadicInt.toAdicCompletion p Rₚ (Field.cyclotomicCharacter Fₚ p g : ℤ_[p])))) :
    letI := darmonPrimeIntegralTateModule p hp ξ
    (((darmonPrimeIntegralTateRepresentation p hp ξ).baseChange L).baseChange E).IsIrreducible := by
  let := realPrimeGenerator_isMaximal p (by omega)
  let := darmonPrimeIntegralTateModule p hp ξ
  let := darmonPrimeIntegralTate_free p hp ξ
  let ρ := (darmonPrimeIntegralTateRepresentation p hp ξ).baseChange L
  let : ρ.IsIrreducible := hirr
  have := AdicCompletion.isDomain_of_isMaximal_span (realPrimeGenerator p)
    (realPrimeGenerator_ne_zero p (by omega))
  have := darmonPrimeIntegralTate_finite p hp ξ
  have hrank : Module.finrank L (L ⊗[Sₚ] (integralTate Fₚ (darmonPrimeFiber p hp ξ).X p)) = 2 := by
    rw [Module.finrank_baseChange]
    exact finrank_darmonPrimeIntegralTate p hp ξ
  exact absoluteIrreducible_of_oddInvolution ρ hrank hL c hc ((hdet c).trans hodd)

/-- A nonzero rational `p`-torsion point on the chosen fibre yields a nonzero
rational point of its actual canonical-prime kernel.  Total ramification makes
a power of the canonical prime generator annihilate the original point; taking
the last nonzero point in this chain gives the kernel point.  This is the
fibrewise algebraic step in [TripathiGoswamiRevised, Lemma `RMtorsion`];
existence of the rational point on this same family is a separate input. -/
theorem exists_darmonPrimeKernel_fixed_of_fiber_pTorsion
    (x : Points Fₚ (AlgebraicClosure Fₚ) (darmonPrimeFiber p hp ξ).X)
    (hx : x ≠ 0) (hpx : p • x = 0)
    (hfix : ∀ g : AlgebraicClosure Fₚ ≃ₐ[Fₚ] AlgebraicClosure Fₚ, g • x = x) :
    ∃ v : Points Fₚ (AlgebraicClosure Fₚ) (darmonPrimeKernel p hp ξ).X,
      v ≠ 0 ∧ ∀ g : AlgebraicClosure Fₚ ≃ₐ[Fₚ] AlgebraicClosure Fₚ, g • v = v := by
  let A := darmonPrimeFiber p hp ξ
  let φ := darmonPrimeFiberRealMultiplication p hp ξ
  let a : Rₚ := realPrimeGenerator p
  let e := (p - 1) / 2
  let := pointsCoefficientModule Fₚ A Rₚ φ
  let : SMulCommClass (AlgebraicClosure Fₚ ≃ₐ[Fₚ] AlgebraicClosure Fₚ) Rₚ
      (Points Fₚ (AlgebraicClosure Fₚ) A.X) :=
    points_coefficient_galois_comm Fₚ A.X Rₚ
      (pointsCoefficientModule_realized Fₚ A Rₚ φ)
  have hmem : a ^ e ∈ (Ideal.span {a}) ^ e := by
    rw [Ideal.span_singleton_pow]
    exact Ideal.subset_span (by simp)
  have hdiv : (p : Rₚ) ∣ a ^ e := by
    rw [span_realPrimeGenerator_pow p (by omega)] at hmem
    exact Ideal.mem_span_singleton.mp hmem
  obtain ⟨u, hu⟩ := hdiv
  have hkill : a ^ e • x = 0 := by
    calc
      a ^ e • x = (u * (p : Rₚ)) • x := by rw [hu, mul_comm]
      _ = u • ((p : Rₚ) • x) := mul_smul _ _ _
      _ = 0 := by rw [Nat.cast_smul_eq_nsmul, hpx, smul_zero]
  have auxiliary : ∀ n : ℕ, ∀ z : Points Fₚ (AlgebraicClosure Fₚ) A.X,
      z ≠ 0 →
      (∀ g : AlgebraicClosure Fₚ ≃ₐ[Fₚ] AlgebraicClosure Fₚ, g • z = z) →
      a ^ n • z = 0 →
      ∃ y : Points Fₚ (AlgebraicClosure Fₚ) A.X,
        y ≠ 0 ∧ a • y = 0 ∧
          ∀ g : AlgebraicClosure Fₚ ≃ₐ[Fₚ] AlgebraicClosure Fₚ, g • y = y := by
    intro n
    induction n with
    | zero =>
        intro z hz _ hzero
        simp only [pow_zero, one_smul] at hzero
        exact (hz hzero).elim
    | succ n ih =>
        intro z hz hzfix hzero
        by_cases haz : a • z = 0
        · exact ⟨z, hz, haz, hzfix⟩
        · apply ih (a • z) haz
          · intro g
            calc
              g • (a • z) = a • (g • z) := smul_comm g a z
              _ = a • z := by rw [hzfix g]
          · simpa only [pow_succ, mul_smul] using hzero
  obtain ⟨y, hy, hay, hyfix⟩ := auxiliary e x hx hfix hkill
  let q : coefficientTorsion Fₚ A.X Rₚ a := ⟨y, hay⟩
  let E := coefficientKernelPointsEquiv Fₚ A Rₚ φ a
  let v := E.symm q
  refine ⟨v, ?_, ?_⟩
  · intro hv
    apply hy
    have hq : q = 0 := by
      calc
        q = E v := (E.apply_symm_apply q).symm
        _ = E 0 := congrArg E hv
        _ = 0 := map_zero E
    exact congrArg Subtype.val hq
  · intro g
    apply E.injective
    apply Subtype.ext
    change (E (g • v) : Points Fₚ (AlgebraicClosure Fₚ) A.X) =
      (E v : Points Fₚ (AlgebraicClosure Fₚ) A.X)
    calc
      (E (g • v) : Points Fₚ (AlgebraicClosure Fₚ) A.X) =
          g • (E v : Points Fₚ (AlgebraicClosure Fₚ) A.X) :=
        coefficientKernelPointsEquiv_galois Fₚ A Rₚ φ a g v
      _ = (E v : Points Fₚ (AlgebraicClosure Fₚ) A.X) := by
        simpa only [v, E.apply_symm_apply] using hyfix g

/-- The actual chosen kernel has trivial and cyclotomic Jordan–Hölder factors
when it has a nonzero fixed point and its own integral Tate determinant is
exactly cyclotomic.  Rank two and determinant reduction are proved here. -/
theorem exists_darmonPrimeKernel_factors_of_integralTate_determinant
    (L : Type*) [Field L] [Algebra Sₚ L] [IsFractionRing Sₚ L]
    (v : Points Fₚ (AlgebraicClosure Fₚ) (darmonPrimeKernel p hp ξ).X)
    (hv : v ≠ 0)
    (hfix : ∀ g : AlgebraicClosure Fₚ ≃ₐ[Fₚ] AlgebraicClosure Fₚ, g • v = v)
    (hdet : ∀ g : AlgebraicClosure Fₚ ≃ₐ[Fₚ] AlgebraicClosure Fₚ,
      letI := darmonPrimeIntegralTateModule p hp ξ
      LinearMap.det ((darmonPrimeIntegralTateRepresentation p hp ξ).baseChange L g) =
        algebraMap Sₚ L
          (TateModule.coefficientPrimeRingEquiv p Rₚ Pₚ ((p - 1) / 2)
            (realPrimeRamification_pos p (by omega)) (span_realPrimeGenerator_pow p (by omega))
              (PadicInt.toAdicCompletion p Rₚ (Field.cyclotomicCharacter Fₚ p g : ℤ_[p])))) :
    letI := realPrimeGenerator_isMaximal p (by omega)
    letI := Ideal.Quotient.field Pₚ
    letI := darmonPrimeKernelModule p hp ξ
    let ρ := darmonPrimeKernelRepresentation p hp ξ
    ∃ T : Subrepresentation ρ,
      Module.finrank kₚ T.toSubmodule = 1 ∧
      Module.finrank kₚ (Points Fₚ (AlgebraicClosure Fₚ) (darmonPrimeKernel p hp ξ).X
        ⧸ T.toSubmodule) = 1 ∧
      T.toRepresentation.IsIrreducible ∧
      (ρ.quotient T.toSubmodule T.apply_mem_toSubmodule).IsIrreducible ∧
      Nonempty ((T.toRepresentation.prod
        (ρ.quotient T.toSubmodule T.apply_mem_toSubmodule)).Equiv
          ((Representation.ofCharacter (K := kₚ) (1 :
            (AlgebraicClosure Fₚ ≃ₐ[Fₚ] AlgebraicClosure Fₚ) →* kₚˣ)).prod
              (Representation.ofCharacter
                (realPrimeResidualCyclotomicCharacter Fₚ p (by omega))))) := by
  exact exists_darmonPrimeKernel_factors p hp ξ v hv hfix
    (finrank_darmonPrimeKernel p hp ξ)
    (darmonPrimeResidualDeterminant_of_integralTate p hp ξ L hdet)

/-- The cohomological dual of the actual chosen kernel has trivial and inverse
cyclotomic Jordan–Hölder factors under those same arithmetic inputs. -/
theorem exists_darmonPrimeKernel_dual_factors_of_integralTate_determinant
    (L : Type*) [Field L] [Algebra Sₚ L] [IsFractionRing Sₚ L]
    (v : Points Fₚ (AlgebraicClosure Fₚ) (darmonPrimeKernel p hp ξ).X)
    (hv : v ≠ 0)
    (hfix : ∀ g : AlgebraicClosure Fₚ ≃ₐ[Fₚ] AlgebraicClosure Fₚ, g • v = v)
    (hdet : ∀ g : AlgebraicClosure Fₚ ≃ₐ[Fₚ] AlgebraicClosure Fₚ,
      letI := darmonPrimeIntegralTateModule p hp ξ
      LinearMap.det ((darmonPrimeIntegralTateRepresentation p hp ξ).baseChange L g) =
        algebraMap Sₚ L
          (TateModule.coefficientPrimeRingEquiv p Rₚ Pₚ ((p - 1) / 2)
            (realPrimeRamification_pos p (by omega)) (span_realPrimeGenerator_pow p (by omega))
              (PadicInt.toAdicCompletion p Rₚ (Field.cyclotomicCharacter Fₚ p g : ℤ_[p])))) :
    letI := realPrimeGenerator_isMaximal p (by omega)
    letI := Ideal.Quotient.field Pₚ
    letI := darmonPrimeKernelModule p hp ξ
    let ρ := darmonPrimeKernelRepresentation p hp ξ
    ∃ T : Subrepresentation ρ.dual,
      Module.finrank kₚ T.toSubmodule = 1 ∧
      Module.finrank kₚ (Module.Dual kₚ
        (Points Fₚ (AlgebraicClosure Fₚ) (darmonPrimeKernel p hp ξ).X)
          ⧸ T.toSubmodule) = 1 ∧
      Representation.IsIrreducible
        (k := kₚ)
        (G := AlgebraicClosure Fₚ ≃ₐ[Fₚ] AlgebraicClosure Fₚ)
        (V := T.toSubmodule) T.toRepresentation ∧
      Representation.IsIrreducible
        (k := kₚ)
        (G := AlgebraicClosure Fₚ ≃ₐ[Fₚ] AlgebraicClosure Fₚ)
        (V := Module.Dual kₚ
          (Points Fₚ (AlgebraicClosure Fₚ) (darmonPrimeKernel p hp ξ).X)
            ⧸ T.toSubmodule)
        (ρ.dual.quotient T.toSubmodule T.apply_mem_toSubmodule) ∧
      Representation.IsSemisimpleRepresentation
        (k := kₚ) (G := AlgebraicClosure Fₚ ≃ₐ[Fₚ] AlgebraicClosure Fₚ)
        (V := T.toSubmodule × (Module.Dual kₚ
          (Points Fₚ (AlgebraicClosure Fₚ) (darmonPrimeKernel p hp ξ).X)
            ⧸ T.toSubmodule))
        (T.toRepresentation.prod
          (ρ.dual.quotient T.toSubmodule T.apply_mem_toSubmodule)) ∧
      Nonempty ((T.toRepresentation.prod
        (ρ.dual.quotient T.toSubmodule T.apply_mem_toSubmodule)).Equiv
          ((Representation.ofCharacter (K := kₚ) (1 :
            (AlgebraicClosure Fₚ ≃ₐ[Fₚ] AlgebraicClosure Fₚ) →* kₚˣ)).prod
              (Representation.ofCharacter
                (realPrimeResidualCyclotomicCharacter Fₚ p (by omega))⁻¹))) := by
  exact exists_realPrimeKernel_dual_factors Fₚ p (by omega)
    (darmonPrimeFiber p hp ξ) (darmonPrimeFiberRealMultiplication p hp ξ)
    v hv hfix (finrank_darmonPrimeKernel p hp ξ)
    (darmonPrimeResidualDeterminant_of_integralTate p hp ξ L hdet)

/-- A fixed `p`-torsion point and the exact determinant on the same chosen fibre
give the covariant residual semisimplification from
[TripathiGoswamiRevised, Proposition `primeresidual`]. -/
theorem exists_darmonPrimeKernel_factors_of_fiber_pTorsion
    (L : Type*) [Field L] [Algebra Sₚ L] [IsFractionRing Sₚ L]
    (x : Points Fₚ (AlgebraicClosure Fₚ) (darmonPrimeFiber p hp ξ).X)
    (hx : x ≠ 0) (hpx : p • x = 0)
    (hfix : ∀ g : AlgebraicClosure Fₚ ≃ₐ[Fₚ] AlgebraicClosure Fₚ, g • x = x)
    (hdet : ∀ g : AlgebraicClosure Fₚ ≃ₐ[Fₚ] AlgebraicClosure Fₚ,
      letI := darmonPrimeIntegralTateModule p hp ξ
      LinearMap.det ((darmonPrimeIntegralTateRepresentation p hp ξ).baseChange L g) =
        algebraMap Sₚ L
          (TateModule.coefficientPrimeRingEquiv p Rₚ Pₚ ((p - 1) / 2)
            (realPrimeRamification_pos p (by omega)) (span_realPrimeGenerator_pow p (by omega))
              (PadicInt.toAdicCompletion p Rₚ (Field.cyclotomicCharacter Fₚ p g : ℤ_[p])))) :
    letI := realPrimeGenerator_isMaximal p (by omega)
    letI := Ideal.Quotient.field Pₚ
    letI := darmonPrimeKernelModule p hp ξ
    let ρ := darmonPrimeKernelRepresentation p hp ξ
    ∃ T : Subrepresentation ρ,
      Nonempty ((T.toRepresentation.prod
        (ρ.quotient T.toSubmodule T.apply_mem_toSubmodule)).Equiv
          ((Representation.ofCharacter (K := kₚ) (1 :
            (AlgebraicClosure Fₚ ≃ₐ[Fₚ] AlgebraicClosure Fₚ) →* kₚˣ)).prod
              (Representation.ofCharacter
                (realPrimeResidualCyclotomicCharacter Fₚ p (by omega))))) := by
  obtain ⟨v, hv, hvfix⟩ :=
    exists_darmonPrimeKernel_fixed_of_fiber_pTorsion p hp ξ x hx hpx hfix
  obtain ⟨T, _, _, _, _, hT⟩ :=
    exists_darmonPrimeKernel_factors_of_integralTate_determinant p hp ξ L v hv hvfix hdet
  exact ⟨T, hT⟩

/-- Dualizing the same chosen-fibre residual factors gives the cohomological
residual semisimplification from [TripathiGoswamiRevised,
Proposition `primeresidual`]. -/
theorem exists_darmonPrimeKernel_dual_factors_of_fiber_pTorsion
    (L : Type*) [Field L] [Algebra Sₚ L] [IsFractionRing Sₚ L]
    (x : Points Fₚ (AlgebraicClosure Fₚ) (darmonPrimeFiber p hp ξ).X)
    (hx : x ≠ 0) (hpx : p • x = 0)
    (hfix : ∀ g : AlgebraicClosure Fₚ ≃ₐ[Fₚ] AlgebraicClosure Fₚ, g • x = x)
    (hdet : ∀ g : AlgebraicClosure Fₚ ≃ₐ[Fₚ] AlgebraicClosure Fₚ,
      letI := darmonPrimeIntegralTateModule p hp ξ
      LinearMap.det ((darmonPrimeIntegralTateRepresentation p hp ξ).baseChange L g) =
        algebraMap Sₚ L
          (TateModule.coefficientPrimeRingEquiv p Rₚ Pₚ ((p - 1) / 2)
            (realPrimeRamification_pos p (by omega)) (span_realPrimeGenerator_pow p (by omega))
              (PadicInt.toAdicCompletion p Rₚ (Field.cyclotomicCharacter Fₚ p g : ℤ_[p])))) :
    letI := realPrimeGenerator_isMaximal p (by omega)
    letI := Ideal.Quotient.field Pₚ
    letI := darmonPrimeKernelModule p hp ξ
    let ρ := darmonPrimeKernelRepresentation p hp ξ
    ∃ T : Subrepresentation ρ.dual,
      Nonempty ((T.toRepresentation.prod
        (ρ.dual.quotient T.toSubmodule T.apply_mem_toSubmodule)).Equiv
          ((Representation.ofCharacter (K := kₚ) (1 :
            (AlgebraicClosure Fₚ ≃ₐ[Fₚ] AlgebraicClosure Fₚ) →* kₚˣ)).prod
              (Representation.ofCharacter
                (realPrimeResidualCyclotomicCharacter Fₚ p (by omega))⁻¹))) := by
  obtain ⟨v, hv, hvfix⟩ :=
    exists_darmonPrimeKernel_fixed_of_fiber_pTorsion p hp ξ x hx hpx hfix
  obtain ⟨T, _, _, _, _, _, hT⟩ :=
    exists_darmonPrimeKernel_dual_factors_of_integralTate_determinant p hp ξ L v hv hvfix hdet
  exact ⟨T, hT⟩

/-- The action on an invariant subspace commutes with a scalar character twist. -/
def characterTwistSubrepresentationEquiv
    {K G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) (χ : G →* Kˣ) (S : Subrepresentation ρ) :
    (Representation.characterTwistSubrepresentationEquiv ρ χ S).toRepresentation.Equiv
      (Representation.characterTwist S.toRepresentation χ) :=
  .mk (LinearEquiv.refl K S.toSubmodule) (by intro g; ext v; rfl)

/-- A scalar character twist distributes over a product of representations. -/
def characterTwistProdEquiv
    {K G V W : Type*} [Field K] [Group G]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (ρ : Representation K G V) (τ : Representation K G W) (χ : G →* Kˣ) :
    (Representation.characterTwist (ρ.prod τ) χ).Equiv
      ((Representation.characterTwist ρ χ).prod
        (Representation.characterTwist τ χ)) :=
  .mk (LinearEquiv.refl K (V × W)) (by
    intro g
    apply LinearMap.ext
    rintro ⟨v, w⟩
    rfl)

/-- An equivariant isomorphism remains equivariant after a common twist. -/
def characterTwistEquiv
    {K G V W : Type*} [Field K] [Group G]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    {ρ : Representation K G V} {τ : Representation K G W}
    (e : ρ.Equiv τ) (χ : G →* Kˣ) :
    (Representation.characterTwist ρ χ).Equiv
      (Representation.characterTwist τ χ) :=
  .mk e.toLinearEquiv (by
    intro g
    ext v
    change e ((χ g : K) • ρ g v) = (χ g : K) • τ g (e v)
    rw [map_smul]
    exact congrArg (fun x : W => (χ g : K) • x)
      (congrArg (fun f : V →ₗ[K] W => f v) (e.isIntertwining' g)))

/-- Twisting a character line multiplies its character. -/
def characterTwistCharacterEquiv
    {K G : Type*} [Field K] [Group G] (χ ψ : G →* Kˣ) :
    (Representation.characterTwist (Representation.ofCharacter ψ) χ).Equiv
      (Representation.ofCharacter (χ * ψ)) :=
  .mk (LinearEquiv.refl K K) (by
    intro g
    apply LinearMap.ext
    intro v
    simp [Representation.characterTwist_apply, Representation.ofCharacter_apply, mul_assoc])

/-- A same-lattice finite-character twist multiplies both Jordan–Hölder
constituents by that character.  The comparison of integral lattices is a
separate arithmetic input, as in [TripathiGoswamiRevised,
Proposition `primeresidual`]. -/
theorem exists_characterTwist_factors
    {K G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) (χ α β : G →* Kˣ)
    (h : ∃ S : Subrepresentation ρ,
      Nonempty ((S.toRepresentation.prod
        (ρ.quotient S.toSubmodule S.apply_mem_toSubmodule)).Equiv
          ((Representation.ofCharacter α).prod (Representation.ofCharacter β)))) :
    ∃ T : Subrepresentation (Representation.characterTwist ρ χ),
      Nonempty ((T.toRepresentation.prod
        ((Representation.characterTwist ρ χ).quotient T.toSubmodule
          T.apply_mem_toSubmodule)).Equiv
            ((Representation.ofCharacter (χ * α)).prod
              (Representation.ofCharacter (χ * β)))) := by
  obtain ⟨S, ⟨e⟩⟩ := h
  let T := Representation.characterTwistSubrepresentationEquiv ρ χ S
  refine ⟨T, ⟨?_⟩⟩
  exact ((characterTwistSubrepresentationEquiv ρ χ S).prod
      (Representation.characterTwistQuotientEquiv ρ χ S)).trans
    ((characterTwistProdEquiv S.toRepresentation
        (ρ.quotient S.toSubmodule S.apply_mem_toSubmodule) χ).symm.trans
      ((characterTwistEquiv e χ).trans
        ((characterTwistProdEquiv (Representation.ofCharacter α)
          (Representation.ofCharacter β) χ).trans
          ((characterTwistCharacterEquiv χ α).prod
            (characterTwistCharacterEquiv χ β)))))

/-- For a residual effective specialization on the same chosen integral
lattice, the cohomological factors become a common finite-character twist.
The fixed point and exact determinant belong to this same chosen fibre;
the displayed action equality is the separate arithmetic RM comparison
after reducing the comparison on its stable lattice.  This is the effective
part of [TripathiGoswamiRevised, Proposition `primeresidual`]. -/
theorem exists_darmonEffective_residual_factors_of_sameLatticeComparison
    (L : Type*) [Field L] [Algebra Sₚ L] [IsFractionRing Sₚ L]
    (x : Points Fₚ (AlgebraicClosure Fₚ) (darmonPrimeFiber p hp ξ).X)
    (hx : x ≠ 0) (hpx : p • x = 0)
    (hfix : ∀ g : AlgebraicClosure Fₚ ≃ₐ[Fₚ] AlgebraicClosure Fₚ, g • x = x)
    (hdet : ∀ g : AlgebraicClosure Fₚ ≃ₐ[Fₚ] AlgebraicClosure Fₚ,
      letI := darmonPrimeIntegralTateModule p hp ξ
      LinearMap.det ((darmonPrimeIntegralTateRepresentation p hp ξ).baseChange L g) =
        algebraMap Sₚ L
          (TateModule.coefficientPrimeRingEquiv p Rₚ Pₚ ((p - 1) / 2)
            (realPrimeRamification_pos p (by omega)) (span_realPrimeGenerator_pow p (by omega))
              (PadicInt.toAdicCompletion p Rₚ (Field.cyclotomicCharacter Fₚ p g : ℤ_[p])))) :
    letI := realPrimeGenerator_isMaximal p (by omega)
    letI := Ideal.Quotient.field Pₚ
    letI := darmonPrimeKernelModule p hp ξ
    let ρ := darmonPrimeKernelRepresentation p hp ξ
    ∀ (χ : (AlgebraicClosure Fₚ ≃ₐ[Fₚ] AlgebraicClosure Fₚ) →* kₚˣ)
      (σ : Representation kₚ (AlgebraicClosure Fₚ ≃ₐ[Fₚ] AlgebraicClosure Fₚ)
        (Module.Dual kₚ (Points Fₚ (AlgebraicClosure Fₚ) (darmonPrimeKernel p hp ξ).X))),
      (∀ g v, σ g v = (χ g : kₚ) • ρ.dual g v) →
      ∃ T : Subrepresentation σ,
        Nonempty ((T.toRepresentation.prod
          (σ.quotient T.toSubmodule T.apply_mem_toSubmodule)).Equiv
            ((Representation.ofCharacter χ).prod
              (Representation.ofCharacter
                (χ * (realPrimeResidualCyclotomicCharacter Fₚ p (by omega))⁻¹)))) := by
  let := realPrimeGenerator_isMaximal p (by omega)
  let := Ideal.Quotient.field Pₚ
  let := darmonPrimeKernelModule p hp ξ
  let ρ := darmonPrimeKernelRepresentation p hp ξ
  dsimp only
  intro χ σ hcomparison
  have hσ : σ = Representation.characterTwist ρ.dual χ := by
    ext g v w
    simpa only [Representation.characterTwist_apply] using
      congrArg (fun f => f w) (hcomparison g v)
  subst σ
  obtain ⟨T, hT⟩ :=
    exists_darmonPrimeKernel_dual_factors_of_fiber_pTorsion p hp ξ L x hx hpx hfix hdet
  obtain ⟨U, hU⟩ := exists_characterTwist_factors ρ.dual χ
    (1 : (AlgebraicClosure Fₚ ≃ₐ[Fₚ] AlgebraicClosure Fₚ) →* kₚˣ)
    (realPrimeResidualCyclotomicCharacter Fₚ p (by omega))⁻¹ ⟨T, hT⟩
  refine ⟨U, ?_⟩
  have hχ : χ * (1 : (AlgebraicClosure Fₚ ≃ₐ[Fₚ] AlgebraicClosure Fₚ) →* kₚˣ) = χ :=
    mul_one χ
  rw [hχ] at hU
  exact hU

end HilbertModularity.Hypergeometric
