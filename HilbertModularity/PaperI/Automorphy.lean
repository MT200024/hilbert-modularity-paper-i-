module
public import HilbertModularity.PaperI.ExactTwist
public import HilbertModularity.Hypergeometric.PrimeEulerMain
public import HilbertModularity.Geometry.GroupScheme.PrimeCohomologicalDeterminant
public import HilbertModularity.NumberTheory.HilbertModularForms.FiniteTwistAnalyticProperties
public import HilbertModularity.NumberTheory.HilbertModularForms.CohomologicalLocalPromotion
public import HilbertModularity.Examples.PrimeFiveRMDualDeterminant

/-! # The RM eigenform, its prescribed twist and the Frobenius determinant -/
public noncomputable section
namespace HilbertModularity.PaperI
open AlgebraicGeometry IsDedekindDomain HilbertModularity.Cyclotomic
open HilbertModularity.Hypergeometric HilbertModularity.HilbertModularForms
open scoped NumberField ValuativeRel
variable (p : ℕ) [Fact p.Prime]

local instance : NormedField (FullConductorCompletion p) :=
  fullConductorCanonicalNormedField p
local instance : NontriviallyNormedField (FullConductorCompletion p) :=
  fullConductorCanonicalNontriviallyNormedField p
local instance : NormedAlgebra ℚ_[p] (FullConductorCompletion p) :=
  fullConductorCanonicalNormedAlgebra p
local instance : IsNonarchimedeanLocalField (FullConductorCompletion p) :=
  NumberField.isNonarchimedeanLocalField_padicCompletion
    (cyclotomicField p) (primeAboveConductor p) p
local instance : CharP (𝒪[FullConductorCompletion p] ⧸ 𝓂[FullConductorCompletion p]) p :=
  NumberField.adicCompletionResidueCharP
    (cyclotomicField p) (primeAboveConductor p) p

attribute [local instance] realFieldAlgebra

variable (hp : 5 ≤ p) (m : ℕ) (hmPos : 0 < m) (hmLt : m < p)
abbrev conductorTate (ξ : ProjectiveLine.Parameter (realCyclotomicField p)) :=
  chosenConductorPlusCoordinateAction p hp m (eulerExponent_coprime_of_prime p m Fact.out hmPos hmLt) ξ

/-- The untwisted RM eigenform at the lifting place. -/
theorem exists_rmEigenform_of_cubic
    (ξ₀ : ProjectiveLine.Parameter ℚ) {A : ℤ} {B : ℕ}
    (hξ : ξ₀.val = (A : ℚ)/B) (hA : A ≠ 0) (hB : B ≠ 0) (hAB : Int.gcd A B=1)
    (hdeep : (p : ℤ)^3 ∣ A ∨ (p : ℤ)^3 ∣ (B : ℤ)-A) :
    ∃ (level : FiniteLevel (realCyclotomicField p)) (μ : AdditiveQuotientMeasure (realCyclotomicField p))
      (C : Type) (hC : Field C), letI := hC
      ∃ hN : NumberField C, letI := hN
      ∃ (φ : AlgebraicGoodPrimeEigenform level μ C) (r : CohomologicalRealization φ p (FullConductorCompletion p)),
        (∃ b : ℝ, ∀ g, ‖φ.form.toFun g‖ ≤ b) ∧ (Set.range φ.form.central_character).Finite ∧
        Nonempty ((conductorTate p hp m hmPos hmLt (darmonRationalParameter p ξ₀)).dual.Equiv r.action) := by
  let ξ := darmonRationalParameter p ξ₀
  have hi := chosenConductorPlusCoordinate_isIrreducible p hp m hmPos hmLt ξ
  let H := chosenConductorCubicWeightTwoInput_of_irreducible p hp m _ ξ₀ hξ hA hB hAB hdeep hi
  exact skinnerWiles_weightTwoEigenform_withAnalyticData p _ (cyclotomicField p) H

/-- The labelled pullbacks at the lifting place, using the original
coordinate representation of the untwisted RM Tate module. -/
def HasConductorPullbacks (ξ : ProjectiveLine.Parameter (realCyclotomicField p)) : Prop :=
  letI : Fact (1 < p) := ⟨by omega⟩
  let L := FullConductorCompletion p
  let w := primeAboveConductor p
  let a := algebraMap (cyclotomicField p) L ((root p) ^ m)
  ∃ (H : Type) (hH : AddCommGroup H), letI := hH
    ∃ hM : Module L H, letI := hM
      Nonempty (QuotientPullbacks ((eulerFamily p hp m hmPos hmLt ξ).action w)
        ((plusFamily p hp m hmPos hmLt (compParameter p ξ)).action w)
        (conductorTate p hp m hmPos hmLt ξ).dual (cyclotomicSign p L) a H)

/-- The dihedral operator identifies the Euler action with the cyclotomic
twist of the native dual RM action used for the modularity lift. -/
theorem conductor_euler_equiv_twisted_dual_of_pullbacks
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (geo : HasConductorPullbacks p hp m hmPos hmLt ξ) :
    letI : Fact (1 < p) := ⟨by omega⟩
    Nonempty (((eulerFamily p hp m hmPos hmLt ξ).action (primeAboveConductor p)).Equiv
      ((conductorTate p hp m hmPos hmLt ξ).dual.characterTwist
        (cyclotomicSign p (FullConductorCompletion p)))) := by
  let : Fact (1 < p) := ⟨by omega⟩
  let L := FullConductorCompletion p
  let a := algebraMap (cyclotomicField p) L ((root p) ^ m)
  have ha : IsPrimitiveRoot a p := ((root_isPrimitiveRoot p).pow_of_coprime m
    (eulerExponent_coprime_of_prime p m Fact.out hmPos hmLt)).map_of_injective
      (algebraMap (cyclotomicField p) L).injective
  have ha0 := ha.ne_zero (NeZero.ne p)
  have hne : a ≠ a⁻¹ := by
    intro h
    have hs : a ^ 2 = 1 := calc
      a ^ 2 = a * a := pow_two _
      _ = a * a⁻¹ := congrArg (a * ·) h
      _ = 1 := mul_inv_cancel₀ ha0
    have hle := Nat.le_of_dvd (by decide : 0 < 2) ((ha.pow_eq_one_iff_dvd 2).mp hs)
    omega
  obtain ⟨H, hH, hM, ⟨D⟩⟩ := geo
  exact ⟨D.eulerComplement.trans (D.complementTwist ha0 hne)⟩

set_option maxHeartbeats 2000000 in
/-- The exact determinant at a good prime follows from the RM pairing and the fact that the twist squares to one. -/
theorem euler_frobenius_det_of_pullbacks (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (geo : HasConductorPullbacks p hp m hmPos hmLt ξ)
    (P : Ideal (𝓞 (realCyclotomicField p))) [P.IsMaximal]
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p)))) [Q.IsMaximal] [Q.LiesOver P]
    (hpQ : (p : 𝓞 (realCyclotomicField p)) ∉ P) :
    LinearMap.det ((eulerFamily p hp m hmPos hmLt ξ).action (primeAboveConductor p)
      (NumberField.geometricFrobenius (realCyclotomicField p) (AlgebraicClosure (realCyclotomicField p)) P Q)) =
      (Nat.card (𝓞 (realCyclotomicField p) ⧸ P) : FullConductorCompletion p) := by
  let : Fact (1 < p) := ⟨by omega⟩
  let K := realCyclotomicField p
  let L := FullConductorCompletion p
  let w := primeAboveConductor p
  let ρ := conductorTate p hp m hmPos hmLt ξ
  let g := NumberField.geometricFrobenius K (AlgebraicClosure K) P Q
  obtain ⟨e⟩ := conductor_euler_equiv_twisted_dual_of_pullbacks p hp m hmPos hmLt ξ geo
  let δ := cyclotomicSign p L
  have hdet (a : AbsoluteGalois K) : LinearMap.det (ρ a) = (Field.cyclotomicCharacterWithCoefficients K p L a : L) :=
    ((chosenConductorDarmonCoordinateEquiv_spectral p hp m _ ξ).determinant_eq a).trans
      (darmonPrimeLabelledTateFamily_det p (by omega) hp p K (ProjectiveLine.puncturedPoint K ξ)
        m _ (cyclotomicField p) (realCyclotomicNormalClosure_le_full p) w L a)
  have hdual := Examples.dualFrobenius_det_of_cyclotomic K p L ρ hdet P Q hpQ
  rw [e.determinant_eq g]
  change LinearMap.det ((δ g : L) • ρ.dual g) = _
  rw [LinearMap.det_smul, Subspace.dual_finrank_eq, Module.finrank_fin_fun, ← hdual]
  have hsign : (δ g : L)^2 = 1 := by
    change (cyclotomicSign p L g : L)^2 = 1
    rw [cyclotomicSign_apply]; split <;> simp
  rw [hsign, one_mul]

local instance : CharZero (FullConductorCompletion p) :=
  charZero_of_injective_algebraMap (algebraMap ℚ_[p] (FullConductorCompletion p)).injective

/-- The coefficients of the two forms lie in a single compositum in the
lifting completion. The equality of adelic functions specifies the twist of
the original eigenform, with geometric reciprocity. -/
def RealizesCyclotomicTwist (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    {level : FiniteLevel (realCyclotomicField p)} {μ : AdditiveQuotientMeasure (realCyclotomicField p)}
    {C : Type} [Field C] [NumberField C] {φ : AlgebraicGoodPrimeEigenform level μ C}
    (r : CohomologicalRealization φ p (FullConductorCompletion p)) : Prop :=
  letI : Fact (1 < p) := ⟨by omega⟩
  let k := algebraMap (cyclotomicField p) (FullConductorCompletion p)
  let M := coefficientCompositum r.coefficientEmbedding k
  let i := coefficientCompositum.right r.coefficientEmbedding k
  let χ := (algebraicCyclotomicSign p (cyclotomicField p)).mapCoefficients i
  ∃ (c : M →+* ℂ) (η : ArithmeticIdeleRealization χ c) (s : HeckeLevelRefinement level η.geometricCharacter)
    (ψ : AlgebraicGoodPrimeEigenform s.level μ M) (r' : CohomologicalRealization ψ p (FullConductorCompletion p)),
    c.comp (coefficientCompositum.left r.coefficientEmbedding k) = φ.complexEmbedding ∧
    (∀ g, ψ.form.toFun g = (η.geometricCharacter.onGL2 g : ℂ)*φ.form.toFun g) ∧
    ψ.complexEmbedding = c ∧ r'.coefficientEmbedding = M.val.toRingHom ∧
    letI : Algebra (cyclotomicField p) M := i.toAlgebra
    ∃ T : EigenformCompatibleSystem ψ, ∀ v : HeightOneSpectrum (𝓞 M),
      Nonempty ((((eulerFamily p hp m hmPos hmLt ξ).extendCoefficients (L := M)).action v).Equiv (T.system.action v))

set_option maxHeartbeats 2000000 in
theorem rm_and_twistedEuler_of_cubic_of_pullbacks
    (ξ₀ : ProjectiveLine.Parameter ℚ) {A : ℤ} {B : ℕ}
    (hξ : ξ₀.val = (A : ℚ)/B) (hA : A ≠ 0) (hB : B ≠ 0) (hAB : Int.gcd A B=1)
    (hdeep : (p : ℤ)^3 ∣ A ∨ (p : ℤ)^3 ∣ (B : ℤ)-A)
    (geometric : HasConductorPullbacks p hp m hmPos hmLt (darmonRationalParameter p ξ₀)) :
    ∃ (level : FiniteLevel (realCyclotomicField p)) (μ : AdditiveQuotientMeasure (realCyclotomicField p))
      (C : Type) (hC : Field C), letI := hC
      ∃ hN : NumberField C, letI := hN
      ∃ (φ : AlgebraicGoodPrimeEigenform level μ C) (r : CohomologicalRealization φ p (FullConductorCompletion p)),
        Nonempty ((conductorTate p hp m hmPos hmLt (darmonRationalParameter p ξ₀)).dual.Equiv r.action) ∧
        RealizesCyclotomicTwist p hp m hmPos hmLt (darmonRationalParameter p ξ₀) r := by
  let : Fact (1 < p) := ⟨by omega⟩
  let : NumberField.IsTotallyReal (realCyclotomicField p) := realCyclotomicField_isTotallyReal p
  let ξ := darmonRationalParameter p ξ₀
  let E := cyclotomicField p
  let L := FullConductorCompletion p
  let w := primeAboveConductor p
  let U := eulerFamily p hp m hmPos hmLt ξ
  let k := algebraMap E L
  let χ := algebraicCyclotomicSign p E
  obtain ⟨level, μ, C, hC, hN, φ, r, hb, hz, ⟨er⟩⟩ :=
    exists_rmEigenform_of_cubic p hp m hmPos hmLt ξ₀ hξ hA hB hAB hdeep
  refine ⟨level, μ, C, hC, hN, φ, r, ⟨er⟩, ?_⟩
  obtain ⟨c, η, s, ψ, r', hc, hf, _, hcomplex, _, hcoeff, _, _, ⟨T⟩, ⟨etwist⟩⟩ :=
    r.exists_finiteTwist_compatibleSystem χ k hb hz
  let M := coefficientCompositum r.coefficientEmbedding k
  let i := coefficientCompositum.right r.coefficientEmbedding k
  refine ⟨c, η, s, ψ, r', hc, hf, hcomplex, hcoeff, T, ?_⟩
  let : Algebra E M := i.toAlgebra
  let δ := cyclotomicSign p L
  obtain ⟨e₀⟩ := conductor_euler_equiv_twisted_dual_of_pullbacks p hp m hmPos hmLt ξ geometric
  rw [algebraicCyclotomicSign_map p E L k] at etwist
  let e := e₀.trans ((er.characterTwist δ).trans
    ((Representation.characterTwistTensorEquiv r.action δ).symm.trans etwist))
  have hi : r'.coefficientEmbedding.comp (algebraMap E M) = k := by
    rw [hcoeff]
    exact coefficientCompositum.val_comp_right r.coefficientEmbedding k
  have hbelow : U.residueCharacteristic w = p := by
    simpa only [U, eulerFamily, chosenCommonEulerCompatibleSystem_eq_common,
      commonEulerCompatibleSystem_residueCharacteristic] using (NumberField.primeBelow_eq_of_liesOver E w p)
  intro v
  apply r'.promote_localComparison (U.extendCoefficients (L := M)) T (U.action w) e _ v
  intro q hq P _ hP hpQ Q _ _
  rw [NumberFieldCompatibleSystem.extendCoefficients_polynomial, Polynomial.map_map, hi]
  exact U.frobenius_charpoly w q (by simpa only [NumberFieldCompatibleSystem.extendCoefficients_bad] using hq)
    P hP (by simpa only [hbelow] using hpQ) Q
end HilbertModularity.PaperI
