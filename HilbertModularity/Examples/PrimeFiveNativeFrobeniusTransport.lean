/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Examples.PrimeFiveJointArithmeticComparison
public import HilbertModularity.Examples.PrimeFiveSelectedRMCharacterPolynomials
public import HilbertModularity.Geometry.GroupScheme.PrimeGoodReduction
public import HilbertModularity.RepresentationTheory.Unramified
public import HilbertModularity.Hypergeometric.GaloisRealizationFrobeniusTransport

/-! # Transport of the selected native RM Frobenius through the fixed closure

The oriented full-cyclotomic prime and its contracted real prime have the
same residue cardinality. On a good native RM factor, the two geometric
Frobenius lifts therefore act identically after identifying the fixed
algebraic closures.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry IsDedekindDomain
open scoped NumberField

namespace HilbertModularity.Examples

open _root_.HilbertModularity.Cyclotomic Hypergeometric GroupScheme

local instance transportFiveFact : Fact (Nat.Prime 5) := ⟨by decide⟩
local notation "K₅" => realCyclotomicField 5
local notation "J₅" => primePlusFiber 5 selectedRMProductFiveLowerBound primeFiveParameter

/-- The inverse closure equivalence also fixes the embedded full
cyclotomic integer ring. -/
theorem primeFiveClosureIntegerEquiv_symm_cyclotomic_algebraMap
    (x : 𝓞 (cyclotomicField 5)) :
    (realEulerClosureIntegerEquiv 5).symm
        (algebraMap (𝓞 (cyclotomicField 5)) (𝓞 Qbar) x) =
      algebraMap (𝓞 (cyclotomicField 5))
        (𝓞 (AlgebraicClosure K₅)) x := by
  apply (realEulerClosureIntegerEquiv 5).injective
  rw [RingEquiv.apply_symm_apply]
  exact (realEulerClosureIntegerEquiv_cyclotomic_algebraMap 5 x).symm

/-- An oriented prime in `Qbar` determines a prime in the fixed real
closure above both the full and contracted real primes. -/
theorem exists_primeFive_realClosurePrime
    (q : HeightOneSpectrum (𝓞 K₅))
    (P : HeightOneSpectrum (𝓞 (cyclotomicField 5)))
    [P.asIdeal.LiesOver q.asIdeal]
    (QbarPrime : Ideal (𝓞 Qbar))
    [QbarPrime.IsMaximal] [QbarPrime.LiesOver P.asIdeal] :
    ∃ Q : Ideal (𝓞 (AlgebraicClosure K₅)),
      ∃ (_ : Q.IsMaximal) (_ : Q.LiesOver q.asIdeal)
        (_ : Q.LiesOver P.asIdeal),
        Q.map (realEulerClosureIntegerEquiv 5) = QbarPrime := by
  let e := realEulerClosureIntegerEquiv 5
  let Q := QbarPrime.map e.symm
  let : Q.IsMaximal := inferInstance
  have hP : Q.LiesOver P.asIdeal := by
    constructor
    rw [Ideal.under_map_ringEquiv QbarPrime (RingEquiv.refl _) e.symm
      primeFiveClosureIntegerEquiv_symm_cyclotomic_algebraMap]
    change P.asIdeal = (QbarPrime.under (𝓞 (cyclotomicField 5))).map
      (RingHom.id (𝓞 (cyclotomicField 5)))
    rw [Ideal.map_id]
    exact (show QbarPrime.LiesOver P.asIdeal from inferInstance).over
  let : Q.LiesOver P.asIdeal := hP
  have hq : Q.LiesOver q.asIdeal :=
    Ideal.LiesOver.trans Q P.asIdeal q.asIdeal
  have hmap : Q.map e = QbarPrime := by
    dsimp only [Q]
    rw [Ideal.map_symm e, Ideal.map_comap_eq_self_of_equiv e]
  exact ⟨Q, inferInstance, hq, hP, hmap⟩

/-- Changing from the fixed real algebraic closure to `Qbar` and then
restricting from the oriented cyclotomic prime preserves geometric
Frobenius on an unramified real-field representation when both residue
fields have the same cardinality. -/
theorem representation_primeFive_orientedFrobenius_eq_realFrobenius
    {L V : Type*} [Field L] [AddCommGroup V] [Module L V]
    (ρ : Representation L (AlgebraicClosure K₅ ≃ₐ[K₅] AlgebraicClosure K₅) V)
    (q : HeightOneSpectrum (𝓞 K₅))
    (P : HeightOneSpectrum (𝓞 (cyclotomicField 5)))
    [P.asIdeal.LiesOver q.asIdeal]
    (Q : Ideal (𝓞 (AlgebraicClosure K₅)))
    [Q.IsMaximal] [Q.LiesOver q.asIdeal] [Q.LiesOver P.asIdeal]
    (QbarPrime : Ideal (𝓞 Qbar))
    [QbarPrime.IsMaximal] [QbarPrime.LiesOver P.asIdeal]
    (hQ : Q.map (realEulerClosureIntegerEquiv 5) = QbarPrime)
    (hcard : Nat.card (𝓞 (cyclotomicField 5) ⧸ P.asIdeal) =
      Nat.card (𝓞 K₅ ⧸ q.asIdeal))
    (hρ : ∀ g ∈ Q.inertia
      (AlgebraicClosure K₅ ≃ₐ[K₅] AlgebraicClosure K₅), ρ g = 1) :
    ρ (primeFiveRealFrobenius P QbarPrime) =
      ρ (NumberField.geometricFrobenius K₅ (AlgebraicClosure K₅)
        q.asIdeal Q) := by
  let e := realEulerClosureIntegerEquiv 5
  let h := primeFiveRealFrobenius P QbarPrime
  have hs (z : 𝓞 (AlgebraicClosure K₅)) :
      e (h⁻¹ • z) =
        (restrictCyclotomicGalois 5
          (absoluteGeometricFrobenius 5 P QbarPrime))⁻¹ • e z := by
    have he := realEulerClosureIntegerEquiv_smul 5
      ((restrictCyclotomicGalois 5
        (absoluteGeometricFrobenius 5 P QbarPrime))⁻¹) z
    simpa only [e, h, primeFiveRealFrobenius_eq_closureTransport,
      realEulerClosureGaloisEquiv_apply, map_inv] using he
  have hspec (z : 𝓞 (AlgebraicClosure K₅)) :
      Ideal.Quotient.mk QbarPrime
          ((restrictCyclotomicGalois 5
            (absoluteGeometricFrobenius 5 P QbarPrime))⁻¹ • e z) =
        (Ideal.Quotient.mk QbarPrime (e z)) ^
          Nat.card (𝓞 (cyclotomicField 5) ⧸ P.asIdeal) := by
    change Ideal.Quotient.mk QbarPrime
        ((absoluteGeometricFrobenius 5 P QbarPrime :
          Qbar ≃ₐ[cyclotomicField 5] Qbar)⁻¹ • e z) = _
    exact absoluteGeometricFrobenius_spec 5 P QbarPrime (e z)
  have hmem (z : 𝓞 (AlgebraicClosure K₅)) :
      h⁻¹ • z - z ^ Nat.card (𝓞 (cyclotomicField 5) ⧸ P.asIdeal) ∈ Q := by
    apply (Ideal.apply_mem_of_equiv_iff (f := e)).mp
    rw [hQ]
    rw [map_sub, map_pow, hs]
    apply (Ideal.Quotient.eq_zero_iff_mem).mp
    simpa only [map_sub, map_pow, sub_eq_zero] using hspec z
  have hres (z : 𝓞 (AlgebraicClosure K₅)) :
      Ideal.Quotient.mk Q (h⁻¹ • z) =
        (Ideal.Quotient.mk Q z) ^ Nat.card (𝓞 K₅ ⧸ q.asIdeal) := by
    have hz := (Ideal.Quotient.eq_zero_iff_mem).mpr (hmem z)
    simpa only [map_sub, map_pow, sub_eq_zero, hcard] using hz
  let r := NumberField.geometricFrobenius K₅ (AlgebraicClosure K₅) q.asIdeal Q
  have hreal (z : 𝓞 (AlgebraicClosure K₅)) :
      Ideal.Quotient.mk Q ((r : AlgebraicClosure K₅ ≃ₐ[K₅] AlgebraicClosure K₅)⁻¹ • z) =
        (Ideal.Quotient.mk Q z) ^ Nat.card (𝓞 K₅ ⧸ q.asIdeal) := by
    simpa only [r, NumberField.geometricFrobenius, inv_inv,
      Subgroup.coe_inv, Subgroup.smul_def] using
        NumberField.arithmeticFrobenius_apply K₅ (AlgebraicClosure K₅)
          q.asIdeal Q z
  have hinv : ρ h⁻¹ =
      ρ ((r : AlgebraicClosure K₅ ≃ₐ[K₅] AlgebraicClosure K₅)⁻¹) := by
    apply Representation.apply_eq_of_inertia_trivial ρ Q hρ
    intro z
    exact (hres z).trans (hreal z).symm
  have hu : ρ.asGroupHom h⁻¹ =
      ρ.asGroupHom ((r : AlgebraicClosure K₅ ≃ₐ[K₅] AlgebraicClosure K₅)⁻¹) :=
    Units.ext hinv
  have hf := congrArg (fun u : (Module.End L V)ˣ =>
    ((u⁻¹ : (Module.End L V)ˣ) : Module.End L V)) hu
  simpa only [h, r, map_inv, inv_inv,
    Units.val_inv_eq_inv_val, Representation.asGroupHom_apply] using hf

/-- Equality of two operators gives equality of their representation
characters, without exposing the carrier's concrete module structure. -/
private theorem representation_character_eq_of_apply_eq
    {L G V : Type*} [Field L] [Group G]
    [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    (ρ : Representation L G V) (g h : G) (heq : ρ g = ρ h) :
    ρ.character g = ρ.character h := by
  exact congrArg (LinearMap.trace L V) heq

/-- On a specified prime of the fixed real closure, the good native
labelled factor has the same character at the oriented and counted
geometric Frobenius lifts. -/
theorem primeFive_nativeCharacter_frobeniusTransport_atPrime
    (L : Type) [Field L] [Algebra ℚ_[5] L] [Algebra ℚ L]
    [IsScalarTower ℚ ℚ_[5] L]
    (hL : ∀ a : K₅, ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (q : HeightOneSpectrum (𝓞 K₅))
    (W : PrimeFiveSelectedSpecialJacobian q)
    (P : HeightOneSpectrum (𝓞 (cyclotomicField 5)))
    [P.asIdeal.LiesOver q.asIdeal]
    (Q : Ideal (𝓞 (AlgebraicClosure K₅)))
    [Q.IsMaximal] [Q.LiesOver q.asIdeal] [Q.LiesOver P.asIdeal]
    (QbarPrime : Ideal (𝓞 Qbar))
    [QbarPrime.IsMaximal] [QbarPrime.LiesOver P.asIdeal]
    (hmap : Q.map (realEulerClosureIntegerEquiv 5) = QbarPrime)
    (hcard : Nat.card (𝓞 (cyclotomicField 5) ⧸ P.asIdeal) =
      Nat.card (𝓞 K₅ ⧸ q.asIdeal))
    (h5q : (5 : 𝓞 K₅) ∉ q.asIdeal)
    (σ : K₅ →ₐ[ℚ] L) :
    ((endomorphismLabelledTate K₅ J₅ 5 K₅ L hL
      (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
        primeFiveParameter) σ).toRepresentation.dual).character
          (primeFiveRealFrobenius P QbarPrime) =
    ((endomorphismLabelledTate K₅ J₅ 5 K₅ L hL
      (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
        primeFiveParameter) σ).toRepresentation.dual).character
          (NumberField.geometricFrobenius K₅ (AlgebraicClosure K₅)
            q.asIdeal Q) := by
  let : IsProper W.model.X.hom := W.proper
  let : Smooth W.model.X.hom := W.smooth
  let : GeometricallyConnected W.model.X.hom := W.connected
  have hgood : q ∉ primePlusFiberBadPrimes 5
      selectedRMProductFiveLowerBound primeFiveParameter :=
    primePlusFiber_not_mem_badPrimes_of_goodReduction 5
      selectedRMProductFiveLowerBound primeFiveParameter q W.model W.genericIso.some
  let ρ := (endomorphismLabelledTate K₅ J₅ 5 K₅ L hL
    (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
      primeFiveParameter) σ).toRepresentation.dual
  have h5q' : ((5 : ℕ) : 𝓞 K₅) ∉ q.asIdeal := by
    simpa only [Nat.cast_ofNat] using h5q
  have hρ : ∀ g ∈ Q.inertia
      (AlgebraicClosure K₅ ≃ₐ[K₅] AlgebraicClosure K₅), ρ g = 1 := by
    intro g hg
    with_reducible
      exact primePlusFiber_labelled_dual_unramified 5
        selectedRMProductFiveLowerBound primeFiveParameter q hgood
        Q 5 h5q' L hL σ g hg
  have heq : ρ (primeFiveRealFrobenius P QbarPrime) =
      ρ (NumberField.geometricFrobenius K₅ (AlgebraicClosure K₅)
        q.asIdeal Q) := by
    with_reducible
      exact representation_primeFive_orientedFrobenius_eq_realFrobenius
        ρ q P Q QbarPrime hmap hcard hρ
  with_reducible
    exact representation_character_eq_of_apply_eq ρ _ _ heq

/-- The special good model and degree-one residue extension identify the
native RM character at the oriented cyclotomic Frobenius with its value at
the counted real-prime Frobenius, for every coefficient label. -/
theorem exists_primeFive_nativeCharacter_frobeniusTransport
    (L : Type) [Field L] [Algebra ℚ_[5] L] [Algebra ℚ L]
    [IsScalarTower ℚ ℚ_[5] L]
    (hL : ∀ a : K₅, ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (q : HeightOneSpectrum (𝓞 K₅))
    (W : PrimeFiveSelectedSpecialJacobian q)
    (P : HeightOneSpectrum (𝓞 (cyclotomicField 5)))
    [P.asIdeal.LiesOver q.asIdeal]
    (QbarPrime : Ideal (𝓞 Qbar))
    [QbarPrime.IsMaximal] [QbarPrime.LiesOver P.asIdeal]
    (hcard : Nat.card (𝓞 (cyclotomicField 5) ⧸ P.asIdeal) =
      Nat.card (𝓞 K₅ ⧸ q.asIdeal))
    (h5q : (5 : 𝓞 K₅) ∉ q.asIdeal) :
    ∃ Q : Ideal (𝓞 (AlgebraicClosure K₅)),
      ∃ (_ : Q.IsMaximal) (_ : Q.LiesOver q.asIdeal),
        ∀ σ : K₅ →ₐ[ℚ] L,
          ((endomorphismLabelledTate K₅ J₅ 5 K₅ L hL
            (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
              primeFiveParameter) σ).toRepresentation.dual).character
                (primeFiveRealFrobenius P QbarPrime) =
          ((endomorphismLabelledTate K₅ J₅ 5 K₅ L hL
            (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
              primeFiveParameter) σ).toRepresentation.dual).character
                (NumberField.geometricFrobenius K₅ (AlgebraicClosure K₅)
                  q.asIdeal Q) := by
  let e := realEulerClosureIntegerEquiv 5
  let Q := QbarPrime.map e.symm
  let : Q.IsMaximal := inferInstance
  have hP : Q.LiesOver P.asIdeal := by
    constructor
    rw [Ideal.under_map_ringEquiv QbarPrime (RingEquiv.refl _) e.symm
      primeFiveClosureIntegerEquiv_symm_cyclotomic_algebraMap]
    change P.asIdeal = (QbarPrime.under (𝓞 (cyclotomicField 5))).map
      (RingHom.id (𝓞 (cyclotomicField 5)))
    rw [Ideal.map_id]
    exact (show QbarPrime.LiesOver P.asIdeal from inferInstance).over
  let : Q.LiesOver P.asIdeal := hP
  have hq : Q.LiesOver q.asIdeal :=
    Ideal.LiesOver.trans Q P.asIdeal q.asIdeal
  let : Q.LiesOver q.asIdeal := hq
  have hmap : Q.map e = QbarPrime := by
    dsimp only [Q]
    rw [Ideal.map_symm e, Ideal.map_comap_eq_self_of_equiv e]
  let : IsProper W.model.X.hom := W.proper
  let : Smooth W.model.X.hom := W.smooth
  let : GeometricallyConnected W.model.X.hom := W.connected
  have hgood : q ∉ primePlusFiberBadPrimes 5
      selectedRMProductFiveLowerBound primeFiveParameter :=
    primePlusFiber_not_mem_badPrimes_of_goodReduction 5
      selectedRMProductFiveLowerBound primeFiveParameter q W.model W.genericIso.some
  refine ⟨Q, inferInstance, hq, ?_⟩
  intro σ
  let ρ := (endomorphismLabelledTate K₅ J₅ 5 K₅ L hL
    (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
      primeFiveParameter) σ).toRepresentation.dual
  have h5q' : ((5 : ℕ) : 𝓞 K₅) ∉ q.asIdeal := by
    simpa only [Nat.cast_ofNat] using h5q
  have hρ : ∀ g ∈ Q.inertia
      (AlgebraicClosure K₅ ≃ₐ[K₅] AlgebraicClosure K₅), ρ g = 1 := by
    intro g hg
    with_reducible
      exact primePlusFiber_labelled_dual_unramified 5
        selectedRMProductFiveLowerBound primeFiveParameter q hgood
        Q 5 h5q' L hL σ g hg
  have heq : ρ (primeFiveRealFrobenius P QbarPrime) =
      ρ (NumberField.geometricFrobenius K₅ (AlgebraicClosure K₅)
        q.asIdeal Q) := by
    with_reducible
      exact representation_primeFive_orientedFrobenius_eq_realFrobenius
        ρ q P Q QbarPrime hmap hcard hρ
  with_reducible
    exact representation_character_eq_of_apply_eq ρ _ _ heq

/-- At an oriented degree-one eleven-prime, the selected Jacobian's two
native RM characters factor the counted polynomial at the same Frobenius
used by the Euler comparison. -/
theorem primeFive_orientedRMCharacterPolynomial11
    (L : Type) [NormedField L] [NormedAlgebra ℚ_[5] L] [Algebra ℚ L]
    [IsScalarTower ℚ ℚ_[5] L]
    (hL : ∀ a : K₅, ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (labels : Fin 2 ≃ (K₅ →ₐ[ℚ] L))
    (q : HeightOneSpectrum (𝓞 K₅))
    (W : PrimeFiveSelectedSpecialJacobian q)
    [Fintype (𝓞 K₅ ⧸ q.asIdeal)]
    (hk : Fintype.card (𝓞 K₅ ⧸ q.asIdeal) = 11)
    (P : HeightOneSpectrum (𝓞 (cyclotomicField 5)))
    [P.asIdeal.LiesOver q.asIdeal]
    (QbarPrime : Ideal (𝓞 Qbar))
    [QbarPrime.IsMaximal] [QbarPrime.LiesOver P.asIdeal]
    (hcard : Nat.card (𝓞 (cyclotomicField 5) ⧸ P.asIdeal) =
      Nat.card (𝓞 K₅ ⧸ q.asIdeal))
    (h5q : (5 : 𝓞 K₅) ∉ q.asIdeal) :
    let g := primeFiveRealFrobenius P QbarPrime
    let ρ₀ := (endomorphismLabelledTate K₅ J₅ 5 K₅ L hL
      (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
        primeFiveParameter) (labels 0)).toRepresentation.dual
    let ρ₁ := (endomorphismLabelledTate K₅ J₅ 5 K₅ L hL
      (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
        primeFiveParameter) (labels 1)).toRepresentation.dual
    (1 - Polynomial.C (ρ₀.character g) * Polynomial.X +
      11 * Polynomial.X ^ 2) *
      (1 - Polynomial.C (ρ₁.character g) * Polynomial.X +
        11 * Polynomial.X ^ 2) = primeFiveNumericalPolynomial11 L := by
  let g := primeFiveRealFrobenius P QbarPrime
  let ρ₀ := (endomorphismLabelledTate K₅ J₅ 5 K₅ L hL
    (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
      primeFiveParameter) (labels 0)).toRepresentation.dual
  let ρ₁ := (endomorphismLabelledTate K₅ J₅ 5 K₅ L hL
    (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
      primeFiveParameter) (labels 1)).toRepresentation.dual
  let e := realEulerClosureIntegerEquiv 5
  let Q := QbarPrime.map e.symm
  let : Q.IsMaximal := inferInstance
  have hP : Q.LiesOver P.asIdeal := by
    constructor
    rw [Ideal.under_map_ringEquiv QbarPrime (RingEquiv.refl _) e.symm
      primeFiveClosureIntegerEquiv_symm_cyclotomic_algebraMap]
    change P.asIdeal = (QbarPrime.under (𝓞 (cyclotomicField 5))).map
      (RingHom.id (𝓞 (cyclotomicField 5)))
    rw [Ideal.map_id]
    exact (show QbarPrime.LiesOver P.asIdeal from inferInstance).over
  let : Q.LiesOver P.asIdeal := hP
  have hq : Q.LiesOver q.asIdeal :=
    Ideal.LiesOver.trans Q P.asIdeal q.asIdeal
  let : Q.LiesOver q.asIdeal := hq
  have hmap : Q.map e = QbarPrime := by
    dsimp only [Q]
    rw [Ideal.map_symm e, Ideal.map_comap_eq_self_of_equiv e]
  let r := NumberField.geometricFrobenius K₅ (AlgebraicClosure K₅) q.asIdeal Q
  have hpoly := by
    with_reducible
      exact primeFiveSelectedRM_characterPolynomial11 L hL labels q W hk Q h5q
  have hchar₀ : ρ₀.character g = ρ₀.character r := by
    with_reducible
      exact primeFive_nativeCharacter_frobeniusTransport_atPrime
        L hL q W P Q QbarPrime hmap hcard h5q (labels 0)
  have hchar₁ : ρ₁.character g = ρ₁.character r := by
    with_reducible
      exact primeFive_nativeCharacter_frobeniusTransport_atPrime
        L hL q W P Q QbarPrime hmap hcard h5q (labels 1)
  with_reducible
    exact characterFactors_transfer ρ₀ ρ₁ g r
      (11 * Polynomial.X ^ 2) (primeFiveNumericalPolynomial11 L)
      hpoly hchar₀ hchar₁


/-- At an oriented degree-one forty-one-prime, the selected Jacobian's two
native RM characters factor the counted polynomial at the same Frobenius
used by the Euler comparison. -/
theorem primeFive_orientedRMCharacterPolynomial41
    (L : Type) [NormedField L] [NormedAlgebra ℚ_[5] L] [Algebra ℚ L]
    [IsScalarTower ℚ ℚ_[5] L]
    (hL : ∀ a : K₅, ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (labels : Fin 2 ≃ (K₅ →ₐ[ℚ] L))
    (q : HeightOneSpectrum (𝓞 K₅))
    (W : PrimeFiveSelectedSpecialJacobian q)
    [Fintype (𝓞 K₅ ⧸ q.asIdeal)]
    (hk : Fintype.card (𝓞 K₅ ⧸ q.asIdeal) = 41)
    (P : HeightOneSpectrum (𝓞 (cyclotomicField 5)))
    [P.asIdeal.LiesOver q.asIdeal]
    (QbarPrime : Ideal (𝓞 Qbar))
    [QbarPrime.IsMaximal] [QbarPrime.LiesOver P.asIdeal]
    (hcard : Nat.card (𝓞 (cyclotomicField 5) ⧸ P.asIdeal) =
      Nat.card (𝓞 K₅ ⧸ q.asIdeal))
    (h5q : (5 : 𝓞 K₅) ∉ q.asIdeal) :
    let g := primeFiveRealFrobenius P QbarPrime
    let ρ₀ := (endomorphismLabelledTate K₅ J₅ 5 K₅ L hL
      (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
        primeFiveParameter) (labels 0)).toRepresentation.dual
    let ρ₁ := (endomorphismLabelledTate K₅ J₅ 5 K₅ L hL
      (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
        primeFiveParameter) (labels 1)).toRepresentation.dual
    (1 - Polynomial.C (ρ₀.character g) * Polynomial.X +
      41 * Polynomial.X ^ 2) *
      (1 - Polynomial.C (ρ₁.character g) * Polynomial.X +
        41 * Polynomial.X ^ 2) = primeFiveNumericalPolynomial41 L := by
  let g := primeFiveRealFrobenius P QbarPrime
  let ρ₀ := (endomorphismLabelledTate K₅ J₅ 5 K₅ L hL
    (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
      primeFiveParameter) (labels 0)).toRepresentation.dual
  let ρ₁ := (endomorphismLabelledTate K₅ J₅ 5 K₅ L hL
    (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
      primeFiveParameter) (labels 1)).toRepresentation.dual
  let e := realEulerClosureIntegerEquiv 5
  let Q := QbarPrime.map e.symm
  let : Q.IsMaximal := inferInstance
  have hP : Q.LiesOver P.asIdeal := by
    constructor
    rw [Ideal.under_map_ringEquiv QbarPrime (RingEquiv.refl _) e.symm
      primeFiveClosureIntegerEquiv_symm_cyclotomic_algebraMap]
    change P.asIdeal = (QbarPrime.under (𝓞 (cyclotomicField 5))).map
      (RingHom.id (𝓞 (cyclotomicField 5)))
    rw [Ideal.map_id]
    exact (show QbarPrime.LiesOver P.asIdeal from inferInstance).over
  let : Q.LiesOver P.asIdeal := hP
  have hq : Q.LiesOver q.asIdeal :=
    Ideal.LiesOver.trans Q P.asIdeal q.asIdeal
  let : Q.LiesOver q.asIdeal := hq
  have hmap : Q.map e = QbarPrime := by
    dsimp only [Q]
    rw [Ideal.map_symm e, Ideal.map_comap_eq_self_of_equiv e]
  let r := NumberField.geometricFrobenius K₅ (AlgebraicClosure K₅) q.asIdeal Q
  have hpoly := by
    with_reducible
      exact primeFiveSelectedRM_characterPolynomial41 L hL labels q W hk Q h5q
  have hchar₀ : ρ₀.character g = ρ₀.character r := by
    with_reducible
      exact primeFive_nativeCharacter_frobeniusTransport_atPrime
        L hL q W P Q QbarPrime hmap hcard h5q (labels 0)
  have hchar₁ : ρ₁.character g = ρ₁.character r := by
    with_reducible
      exact primeFive_nativeCharacter_frobeniusTransport_atPrime
        L hL q W P Q QbarPrime hmap hcard h5q (labels 1)
  with_reducible
    exact characterFactors_transfer ρ₀ ρ₁ g r
      (41 * Polynomial.X ^ 2) (primeFiveNumericalPolynomial41 L)
      hpoly hchar₀ hchar₁


end HilbertModularity.Examples
