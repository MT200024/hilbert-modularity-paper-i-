/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.GaloisRealizationCompatibleSystem
public import HilbertModularity.RingTheory.Ideal.InertiaEquiv
public import HilbertModularity.RingTheory.Ideal.UnderEquiv
public import HilbertModularity.NumberTheory.AbsoluteFrobenius
public import Mathlib.RingTheory.Frobenius

/-! # Geometric Frobenius across the chosen algebraic-closure models

The selected Euler comparison uses the cyclotomic absolute closure `Qbar`,
whereas the compatible-system endpoint uses the algebraic closure of the
real field. The latter is equipped here with the cyclotomic embedding induced
by the fixed closure equivalence. Both models then use the same coefficient
embedding, and their Frobenius lifts differ only by inertia.
-/

public noncomputable section

open AlgebraicGeometry IsDedekindDomain
open HilbertModularity.Cyclotomic
open HilbertModularity.LocalSpecialization
open scoped NumberField

namespace HilbertModularity.Hypergeometric

universe u

variable (N : ℕ) [NeZero N]

local instance (w : HeightOneSpectrum (𝓞 (cyclotomicField N))) :
    NontriviallyNormedField (w.adicCompletion (cyclotomicField N)) :=
  Valued.toNontriviallyNormedField (w.adicCompletion (cyclotomicField N))
    (WithZero (Multiplicative ℤ))

/-- The cyclotomic coefficient field inside the real field's chosen
algebraic closure, transported from its canonical inclusion in `Qbar`. -/
def realEulerCyclotomicClosureEmbedding :
    cyclotomicField N →+* AlgebraicClosure (realCyclotomicField N) :=
  (realEulerClosureEquiv N).symm.toRingHom.comp
    (algebraMap (cyclotomicField N) Qbar)

instance realEulerCyclotomicClosureAlgebra :
    Algebra (cyclotomicField N) (AlgebraicClosure (realCyclotomicField N)) :=
  (realEulerCyclotomicClosureEmbedding N).toAlgebra

instance realEulerCyclotomicClosureTower :
    IsScalarTower (realCyclotomicField N) (cyclotomicField N)
      (AlgebraicClosure (realCyclotomicField N)) := by
  apply IsScalarTower.of_algebraMap_eq
  intro x
  apply (realEulerClosureEquiv N).injective
  change (realEulerClosureEquiv N)
      (algebraMap (realCyclotomicField N)
        (AlgebraicClosure (realCyclotomicField N)) x) =
    (realEulerClosureEquiv N)
      ((realEulerClosureEquiv N).symm
        (algebraMap (cyclotomicField N) Qbar
          (algebraMap (realCyclotomicField N) (cyclotomicField N) x)))
  rw [RingEquiv.apply_symm_apply, realEulerClosureEquiv_algebraMap]
  rfl

/-- The fixed closure isomorphism, now viewed over the full cyclotomic
coefficient field. This is the closure model used for trace transport. -/
def realEulerCyclotomicClosureAlgEquiv :
    AlgebraicClosure (realCyclotomicField N) ≃ₐ[cyclotomicField N] Qbar :=
  AlgEquiv.ofRingEquiv (f := realEulerClosureEquiv N) (by
    intro x
    change (realEulerClosureEquiv N)
      ((realEulerClosureEquiv N).symm
        (algebraMap (cyclotomicField N) Qbar x)) =
      algebraMap (cyclotomicField N) Qbar x
    exact RingEquiv.apply_symm_apply _ _)

instance realEulerCyclotomicClosure_isGalois :
    IsGalois (cyclotomicField N)
      (AlgebraicClosure (realCyclotomicField N)) := by
  exact IsGalois.of_algEquiv (realEulerCyclotomicClosureAlgEquiv N).symm

/-- The induced equivalence of integer rings fixes the full cyclotomic
coefficient ring under the transported algebra structure. -/
theorem realEulerClosureIntegerEquiv_cyclotomic_algebraMap
    (x : 𝓞 (cyclotomicField N)) :
    realEulerClosureIntegerEquiv N
        (algebraMap (𝓞 (cyclotomicField N))
          (𝓞 (AlgebraicClosure (realCyclotomicField N))) x) =
      algebraMap (𝓞 (cyclotomicField N)) (𝓞 Qbar) x := by
  apply Subtype.ext
  calc
    ((realEulerClosureIntegerEquiv N
        (algebraMap (𝓞 (cyclotomicField N))
          (𝓞 (AlgebraicClosure (realCyclotomicField N))) x) : 𝓞 Qbar) : Qbar) =
        realEulerClosureEquiv N
          (algebraMap (𝓞 (cyclotomicField N))
            (𝓞 (AlgebraicClosure (realCyclotomicField N))) x :
              AlgebraicClosure (realCyclotomicField N)) :=
      realEulerClosureIntegerEquiv_apply N _
    _ = algebraMap (cyclotomicField N) Qbar x := by
      change realEulerClosureEquiv N
        (algebraMap (cyclotomicField N)
          (AlgebraicClosure (realCyclotomicField N)) x) = _
      exact (realEulerCyclotomicClosureAlgEquiv N).commutes x
    _ = ((algebraMap (𝓞 (cyclotomicField N)) (𝓞 Qbar) x : 𝓞 Qbar) : Qbar) :=
      (rfl)

/-- A prime over the cyclotomic field remains over the same prime when the
two algebraic-closure models are identified over that field. -/
theorem realEulerClosureIntegerEquiv_liesOver_cyclotomic
    (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField N))))
    [Q.IsMaximal] [Q.LiesOver P.asIdeal] :
    (Q.map (realEulerClosureIntegerEquiv N)).LiesOver P.asIdeal := by
  constructor
  rw [Ideal.under_map_ringEquiv Q (RingEquiv.refl _)
    (realEulerClosureIntegerEquiv N)
    (realEulerClosureIntegerEquiv_cyclotomic_algebraMap N)]
  change P.asIdeal = (Q.under (𝓞 (cyclotomicField N))).map
    (RingHom.id (𝓞 (cyclotomicField N)))
  rw [Ideal.map_id]
  exact (show Q.LiesOver P.asIdeal from inferInstance).over

/-- Conjugate an automorphism of the real closure fixing the cyclotomic
field to an automorphism of `Qbar` fixing the same field. -/
def realEulerCyclotomicClosureGaloisMap
    (g : AlgebraicClosure (realCyclotomicField N) ≃ₐ[cyclotomicField N]
      AlgebraicClosure (realCyclotomicField N)) :
    Qbar ≃ₐ[cyclotomicField N] Qbar :=
  (((realEulerCyclotomicClosureAlgEquiv N).symm.trans g).trans
    (realEulerCyclotomicClosureAlgEquiv N))

/-- Conjugation of the full cyclotomic Galois group is equivariant on
algebraic integers, using the same map as the prime transport. -/
theorem realEulerClosureIntegerEquiv_cyclotomic_smul
    (g : AlgebraicClosure (realCyclotomicField N) ≃ₐ[cyclotomicField N]
      AlgebraicClosure (realCyclotomicField N))
    (z : 𝓞 (AlgebraicClosure (realCyclotomicField N))) :
    realEulerClosureIntegerEquiv N (g • z) =
      realEulerCyclotomicClosureGaloisMap N g • realEulerClosureIntegerEquiv N z := by
  apply Subtype.ext
  calc
    ((realEulerClosureIntegerEquiv N (g • z) : 𝓞 Qbar) : Qbar) =
        realEulerClosureEquiv N (g (z : AlgebraicClosure (realCyclotomicField N))) := by
      exact realEulerClosureIntegerEquiv_apply N _
    _ = realEulerCyclotomicClosureGaloisMap N g
          (realEulerClosureEquiv N z) := by
      change (realEulerClosureEquiv N) (g (z : AlgebraicClosure (realCyclotomicField N))) =
        (realEulerClosureEquiv N)
          (g ((realEulerClosureEquiv N).symm (realEulerClosureEquiv N z)))
      rw [RingEquiv.symm_apply_apply]
    _ = ((realEulerCyclotomicClosureGaloisMap N g •
          realEulerClosureIntegerEquiv N z : 𝓞 Qbar) : Qbar) := by
      change realEulerCyclotomicClosureGaloisMap N g (realEulerClosureEquiv N z) =
        realEulerCyclotomicClosureGaloisMap N g
          ((realEulerClosureIntegerEquiv N z : 𝓞 Qbar) : Qbar)
      rw [realEulerClosureIntegerEquiv_apply]

/-- The arithmetic Frobenius congruence survives transport between the two
closure models over the *same* cyclotomic field. This is a direct application
of the equivariant integer-ring isomorphism, with the residue-field cardinal
fixed by contraction to the same finite prime. -/
theorem realEulerClosure_isArithFrobAt_map
    (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField N))))
    [Q.IsMaximal] [Q.LiesOver P.asIdeal]
    (g : AlgebraicClosure (realCyclotomicField N) ≃ₐ[cyclotomicField N]
      AlgebraicClosure (realCyclotomicField N))
    (hg : IsArithFrobAt (𝓞 (cyclotomicField N)) g Q) :
    IsArithFrobAt (𝓞 (cyclotomicField N))
      (realEulerCyclotomicClosureGaloisMap N g)
      (Q.map (realEulerClosureIntegerEquiv N)) := by
  let e := realEulerClosureIntegerEquiv N
  let Q' := Q.map e
  have hQ' : Q'.LiesOver P.asIdeal :=
    realEulerClosureIntegerEquiv_liesOver_cyclotomic N P Q
  have hcard : Nat.card (𝓞 (cyclotomicField N) ⧸ Q'.under (𝓞 (cyclotomicField N))) =
      Nat.card (𝓞 (cyclotomicField N) ⧸ Q.under (𝓞 (cyclotomicField N))) := by
    rw [hQ'.over.symm, (show Q.LiesOver P.asIdeal from inferInstance).over.symm]
  intro y
  obtain ⟨x, rfl⟩ := e.surjective y
  have hx : g • x - x ^ Nat.card
      (𝓞 (cyclotomicField N) ⧸ Q.under (𝓞 (cyclotomicField N))) ∈ Q :=
    hg x
  have hmem : e (g • x - x ^ Nat.card
      (𝓞 (cyclotomicField N) ⧸ Q.under (𝓞 (cyclotomicField N)))) ∈ Q' :=
    (Ideal.apply_mem_of_equiv_iff (f := e)).mpr hx
  change realEulerCyclotomicClosureGaloisMap N g • e x -
    (e x) ^ Nat.card
      (𝓞 (cyclotomicField N) ⧸ Q'.under (𝓞 (cyclotomicField N))) ∈ Q'
  rw [hcard, ← realEulerClosureIntegerEquiv_cyclotomic_smul]
  simpa only [map_sub, map_pow] using hmem

/-- Conjugation preserves inverse Galois automorphisms. -/
theorem realEulerCyclotomicClosureGaloisMap_inv
    (g : AlgebraicClosure (realCyclotomicField N) ≃ₐ[cyclotomicField N]
      AlgebraicClosure (realCyclotomicField N)) :
    realEulerCyclotomicClosureGaloisMap N g⁻¹ =
      (realEulerCyclotomicClosureGaloisMap N g)⁻¹ := by
  apply AlgEquiv.ext
  intro x
  change (realEulerClosureEquiv N)
      (g⁻¹ ((realEulerClosureEquiv N).symm x)) =
    (realEulerClosureEquiv N)
      (g⁻¹ ((realEulerClosureEquiv N).symm x))
  rfl

/-- The chosen real-closure Galois map sends the transported cyclotomic
automorphism back to the original one after restriction to the real field. -/
theorem realEulerCyclotomicClosureGaloisMap_restrict
    (g : AlgebraicClosure (realCyclotomicField N) ≃ₐ[cyclotomicField N]
      AlgebraicClosure (realCyclotomicField N)) :
    realEulerClosureGaloisHom N
        (restrictCyclotomicGalois N
          (realEulerCyclotomicClosureGaloisMap N g)) =
      g.restrictScalars (realCyclotomicField N) := by
  apply AlgEquiv.ext
  intro x
  rw [realEulerClosureGaloisHom_apply]
  change (realEulerClosureEquiv N).symm
      ((realEulerClosureEquiv N)
        (g ((realEulerClosureEquiv N).symm
          (realEulerClosureEquiv N x)))) = g x
  simp

/-- A residue power equation at a specified lower prime gives the standard
arithmetic-Frobenius predicate at its actual upper prime. -/
theorem isArithFrobAt_of_quotient_pow
    {A B G : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
    (p : Ideal A) (Q : Ideal B) [Q.LiesOver p] (g : G)
    (hg : ∀ b : B, Ideal.Quotient.mk Q (g • b) =
      (Ideal.Quotient.mk Q b) ^ Nat.card (A ⧸ p)) :
    IsArithFrobAt A g Q := by
  intro b
  rw [show Q.under A = p from (show Q.LiesOver p from inferInstance).over.symm]
  apply (Ideal.Quotient.eq_zero_iff_mem).mp
  simp only [map_sub, map_pow]
  exact sub_eq_zero.mpr (hg b)

/-- The chosen geometric lift in the real closure has inverse arithmetic
Frobenius, with the actual cyclotomic residue-field norm. -/
theorem realEulerClosure_geometricFrobenius_inv_isArithFrobAt
    (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField N))))
    [Q.IsMaximal] [Q.LiesOver P.asIdeal] :
    IsArithFrobAt (𝓞 (cyclotomicField N))
      ((NumberField.geometricFrobenius (cyclotomicField N)
        (AlgebraicClosure (realCyclotomicField N)) P.asIdeal Q)⁻¹ :
          AlgebraicClosure (realCyclotomicField N) ≃ₐ[cyclotomicField N]
            AlgebraicClosure (realCyclotomicField N)) Q := by
  apply isArithFrobAt_of_quotient_pow P.asIdeal Q _
  intro b
  simpa only [NumberField.geometricFrobenius, inv_inv, Subgroup.coe_inv,
    Subgroup.smul_def]
    using NumberField.arithmeticFrobenius_apply (cyclotomicField N)
      (AlgebraicClosure (realCyclotomicField N)) P.asIdeal Q b

/-- The existing `Qbar` geometric lift used by the Euler trace theorem
has inverse arithmetic Frobenius at its specified cyclotomic prime. -/
theorem absoluteGeometricFrobenius_inv_isArithFrobAt
    (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    (Q : Ideal (𝓞 Qbar)) [Q.IsMaximal] [Q.LiesOver P.asIdeal] :
    IsArithFrobAt (𝓞 (cyclotomicField N))
      ((absoluteGeometricFrobenius N P Q)⁻¹ :
        Qbar ≃ₐ[cyclotomicField N] Qbar) Q := by
  apply isArithFrobAt_of_quotient_pow P.asIdeal Q _
  intro b
  simpa only [Subgroup.coe_inv, Subgroup.smul_def] using
    absoluteGeometricFrobenius_spec N P Q b

/-- The two geometric lifts at a transported prime differ by inertia.
Both inverses have the same arithmetic residue-power action; the conclusion
is [mathlib, `IsArithFrobAt.mul_inv_mem_inertia`] in the actual upper integer
ring, with no identification of their chosen representatives. -/
theorem realEuler_geometricFrobenius_mul_mem_inertia
    (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField N))))
    [Q.IsMaximal] [Q.LiesOver P.asIdeal] :
    let Q' := Q.map (realEulerClosureIntegerEquiv N)
    letI : Q'.IsMaximal := inferInstance
    letI : Q'.LiesOver P.asIdeal :=
      realEulerClosureIntegerEquiv_liesOver_cyclotomic N P Q
    let g := realEulerCyclotomicClosureGaloisMap N
      (NumberField.geometricFrobenius (cyclotomicField N)
        (AlgebraicClosure (realCyclotomicField N)) P.asIdeal Q :
          AlgebraicClosure (realCyclotomicField N) ≃ₐ[cyclotomicField N]
            AlgebraicClosure (realCyclotomicField N))
    g⁻¹ * (absoluteGeometricFrobenius N P Q' :
      Qbar ≃ₐ[cyclotomicField N] Qbar) ∈
        Q'.inertia (Qbar ≃ₐ[cyclotomicField N] Qbar) := by
  dsimp only
  let Q' := Q.map (realEulerClosureIntegerEquiv N)
  let : Q'.IsMaximal := inferInstance
  let : Q'.LiesOver P.asIdeal :=
    realEulerClosureIntegerEquiv_liesOver_cyclotomic N P Q
  let gΩ : AlgebraicClosure (realCyclotomicField N) ≃ₐ[cyclotomicField N]
      AlgebraicClosure (realCyclotomicField N) :=
    NumberField.geometricFrobenius (cyclotomicField N)
      (AlgebraicClosure (realCyclotomicField N)) P.asIdeal Q
  have h₁ : IsArithFrobAt (𝓞 (cyclotomicField N))
      (realEulerCyclotomicClosureGaloisMap N gΩ)⁻¹ Q' := by
    rw [← realEulerCyclotomicClosureGaloisMap_inv]
    exact realEulerClosure_isArithFrobAt_map N P Q gΩ⁻¹
      (realEulerClosure_geometricFrobenius_inv_isArithFrobAt N P Q)
  have h₂ := absoluteGeometricFrobenius_inv_isArithFrobAt N P Q'
  simpa only [inv_inv] using h₁.mul_inv_mem_inertia h₂

/-- At a canonical good prime, changing from the real closure to `Qbar`
does not change the selected descent's geometric-Frobenius operator. The
two lifts have the same residue action at the transported cyclotomic prime
and differ by inertia, on which the chosen cohomological descent is trivial.
This keeps the raw GPRV trace on the exact same coefficient label. -/
theorem ProperEulerRealDescent.geometricFrobenius_closureTransport
    (m ℓ : ℕ) [Fact ℓ.Prime]
    (L : Type u) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra ℚ_[ℓ] L] [ContinuousSMul ℚ_[ℓ] L]
    (ι : cyclotomicField N →+* L)
    (hN : N.Prime) (h5 : 5 ≤ N) (hm : 0 < m) (hmN : m < N)
    (𝒞 : SmoothProperEulerFamily N m)
    (D : ProperEulerRealDescent N m ℓ L ι 𝒞)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    (q : HeightOneSpectrum (𝓞 (realCyclotomicField N)))
    (hq : q ∉ commonEulerBadPrimes N ξ)
    (hℓq : (ℓ : 𝓞 (realCyclotomicField N)) ∉ q.asIdeal)
    (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    [P.asIdeal.LiesOver q.asIdeal]
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField N))))
    [Q.IsMaximal] [Q.LiesOver P.asIdeal] :
    let Q' := Q.map (realEulerClosureIntegerEquiv N)
    letI : Q'.IsMaximal := inferInstance
    letI : Q'.LiesOver P.asIdeal :=
      realEulerClosureIntegerEquiv_liesOver_cyclotomic N P Q
    D.localSystem.arithmeticRepresentation (ProjectiveLine.puncturedPoint _ ξ)
      ((NumberField.geometricFrobenius (cyclotomicField N)
        (AlgebraicClosure (realCyclotomicField N)) P.asIdeal Q :
          AlgebraicClosure (realCyclotomicField N) ≃ₐ[cyclotomicField N]
            AlgebraicClosure (realCyclotomicField N)).restrictScalars
              (realCyclotomicField N)) =
    D.localSystem.arithmeticRepresentation (ProjectiveLine.puncturedPoint _ ξ)
      ((realEulerClosureGaloisHom N).comp (restrictCyclotomicGalois N)
        (absoluteGeometricFrobenius N P Q')) := by
  dsimp only
  let Q' := Q.map (realEulerClosureIntegerEquiv N)
  let : Q'.IsMaximal := inferInstance
  let : Q'.LiesOver P.asIdeal :=
    realEulerClosureIntegerEquiv_liesOver_cyclotomic N P Q
  let gΩ : AlgebraicClosure (realCyclotomicField N) ≃ₐ[cyclotomicField N]
      AlgebraicClosure (realCyclotomicField N) :=
    NumberField.geometricFrobenius (cyclotomicField N)
      (AlgebraicClosure (realCyclotomicField N)) P.asIdeal Q
  let g' := realEulerCyclotomicClosureGaloisMap N gΩ
  let a : Qbar ≃ₐ[cyclotomicField N] Qbar := absoluteGeometricFrobenius N P Q'
  let ρ := (D.localSystem.arithmeticRepresentation
    (ProjectiveLine.puncturedPoint _ ξ)).comp
      ((realEulerClosureGaloisHom N).comp (restrictCyclotomicGalois N))
  have hq' : q ∉ badPrimesBelow (K := realCyclotomicField N)
      (realEulerParameter N ξ) (N * ℓ) :=
    commonEulerBadPrimes_away_product N ξ ℓ q hq hℓq
  have htriv : ∀ h ∈ Q'.inertia (Qbar ≃ₐ[cyclotomicField N] Qbar),
      ρ h = 1 := by
    intro h hh
    have hhK : restrictCyclotomicGalois N h ∈
        Q'.inertia (Qbar ≃ₐ[realCyclotomicField N] Qbar) := by
      exact Ideal.mem_inertia.mpr (Ideal.mem_inertia.mp hh)
    exact D.inertia_eq_one_outside_badPrimes N m ℓ L ι hN h5 hm hmN
      𝒞 ξ q hq' P Q' (restrictCyclotomicGalois N h) hhK
  have hi : ρ (g'⁻¹ * a) = 1 := htriv _ <|
    realEuler_geometricFrobenius_mul_mem_inertia N P Q
  have heq : ρ g' = ρ a := by
    calc
      ρ g' = ρ g' * ρ (g'⁻¹ * a) := by rw [hi, mul_one]
      _ = ρ (g' * (g'⁻¹ * a)) := (map_mul ρ g' _).symm
      _ = ρ a := by simp only [mul_inv_cancel_left]
  change D.localSystem.arithmeticRepresentation
      (ProjectiveLine.puncturedPoint _ ξ)
      (gΩ.restrictScalars (realCyclotomicField N)) =
    D.localSystem.arithmeticRepresentation
      (ProjectiveLine.puncturedPoint _ ξ)
      ((realEulerClosureGaloisHom N).comp (restrictCyclotomicGalois N) a)
  change D.localSystem.arithmeticRepresentation
      (ProjectiveLine.puncturedPoint _ ξ)
      (realEulerClosureGaloisHom N (restrictCyclotomicGalois N g')) =
    D.localSystem.arithmeticRepresentation
      (ProjectiveLine.puncturedPoint _ ξ)
      ((realEulerClosureGaloisHom N).comp (restrictCyclotomicGalois N) a) at heq
  dsimp only [g'] at heq
  rw [realEulerCyclotomicClosureGaloisMap_restrict] at heq
  exact heq

/-- The compatible system assembled from the one chosen Euler quotient has
the exact normalized geometric-Frobenius trace at an upper cyclotomic prime.
The proof uses the selected descent's fixed-projector trace, the proved
closure-model lift transport and coordinate invariance of trace. In
particular the coefficient label is the canonical map from the *same*
cyclotomic number field at every completion. -/
theorem commonEulerCompatibleSystem_geometricFrobenius_trace
    (m : ℕ) (𝒞 : SmoothProperEulerFamily N m)
    (R : CommonRealEulerQuotientRealization N m 𝒞)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    (hN : N.Prime) (h5 : 5 ≤ N) (hm : 0 < m) (hmN : m < N)
    (w : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    (q : HeightOneSpectrum (𝓞 (realCyclotomicField N)))
    (hq : q ∉ (commonEulerCompatibleSystem N m 𝒞 R ξ hN h5 hm hmN).bad)
    (hℓq : (NumberField.primeBelow (cyclotomicField N) w :
      𝓞 (realCyclotomicField N)) ∉ q.asIdeal)
    (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    [P.asIdeal.LiesOver q.asIdeal]
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (hξ : P.GoodUnit (realEulerParameter N ξ))
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField N))))
    [Q.IsMaximal] [Q.LiesOver P.asIdeal] :
    let g := NumberField.geometricFrobenius (cyclotomicField N)
      (AlgebraicClosure (realCyclotomicField N)) P.asIdeal Q
    LinearMap.trace (w.adicCompletion (cyclotomicField N))
        (Fin 2 → w.adicCompletion (cyclotomicField N))
        ((commonEulerCompatibleSystem N m 𝒞 R ξ hN h5 hm hmN).action w
          (AlgEquiv.restrictScalarsHom (realCyclotomicField N)
            (g : AlgebraicClosure (realCyclotomicField N) ≃ₐ[cyclotomicField N]
              AlgebraicClosure (realCyclotomicField N)))) =
      algebraMap (cyclotomicField N) (w.adicCompletion (cyclotomicField N))
        (normalizedCyclotomicEulerTrace N P.asIdeal hP m
          (P.specialization (realEulerParameter N ξ) hξ.valuation_eq_one.le)) := by
  let : Fact (NumberField.primeBelow (cyclotomicField N) w).Prime :=
    NumberField.primeBelow_prime (cyclotomicField N) w
  let D := commonEulerCompletionDescent N m 𝒞 R w
  let Q' := Q.map (realEulerClosureIntegerEquiv N)
  let : Q'.IsMaximal := inferInstance
  let : Q'.LiesOver P.asIdeal :=
    realEulerClosureIntegerEquiv_liesOver_cyclotomic N P Q
  have hq' : q ∉ commonEulerBadPrimes N ξ := by
    simpa only [commonEulerCompatibleSystem_bad_eq_common] using hq
  have hℓP :
      (NumberField.primeBelow (cyclotomicField N) w :
        𝓞 (cyclotomicField N)) ∉ P.asIdeal := by
    intro hmem
    apply hℓq
    apply (Ideal.mem_of_liesOver P.asIdeal q.asIdeal
      (NumberField.primeBelow (cyclotomicField N) w :
        𝓞 (realCyclotomicField N))).mpr
    simpa only [map_natCast] using hmem
  have ht := D.geometricFrobenius_closureTransport N m
    (NumberField.primeBelow (cyclotomicField N) w)
    (w.adicCompletion (cyclotomicField N))
    (algebraMap (cyclotomicField N) (w.adicCompletion (cyclotomicField N)))
    hN h5 hm hmN 𝒞 ξ q hq' hℓq P Q
  have hraw := D.geometricFrobenius_trace_eq_normalizedEulerTrace N m
    (NumberField.primeBelow (cyclotomicField N) w)
    (w.adicCompletion (cyclotomicField N))
    (algebraMap (cyclotomicField N) (w.adicCompletion (cyclotomicField N)))
    hN h5 hm hmN 𝒞 P hP hℓP Q' ξ hξ
  let g := NumberField.geometricFrobenius (cyclotomicField N)
    (AlgebraicClosure (realCyclotomicField N)) P.asIdeal Q
  calc
    _ = LinearMap.trace (w.adicCompletion (cyclotomicField N))
        (Fin 2 → w.adicCompletion (cyclotomicField N))
        (commonEulerCompletionAction N m 𝒞 R ξ w
          (AlgEquiv.restrictScalarsHom (realCyclotomicField N)
            (g : AlgebraicClosure (realCyclotomicField N) ≃ₐ[cyclotomicField N]
              AlgebraicClosure (realCyclotomicField N)))) := by
      rw [commonEulerCompatibleSystem_action]
    _ = LinearMap.trace (w.adicCompletion (cyclotomicField N)) _
        (D.localSystem.arithmeticRepresentation
          (ProjectiveLine.puncturedPoint _ ξ)
          ((g : AlgebraicClosure (realCyclotomicField N) ≃ₐ[cyclotomicField N]
            AlgebraicClosure (realCyclotomicField N)).restrictScalars
              (realCyclotomicField N))) := by
      exact commonEulerCompletionAction_trace N m 𝒞 R ξ w _
    _ = LinearMap.trace (w.adicCompletion (cyclotomicField N)) _
        (D.localSystem.arithmeticRepresentation
          (ProjectiveLine.puncturedPoint _ ξ)
          ((realEulerClosureGaloisHom N).comp (restrictCyclotomicGalois N)
            (absoluteGeometricFrobenius N P Q'))) := congrArg _ ht
    _ = _ := hraw

/-- Exact trace premise for the all-good-unit-prime eigenform endpoint,
specialized to the chosen Euler compatible system. The extension `ι` may
vary with the coefficient place, but it must extend the canonical embedding
of the *same* cyclotomic coefficient field. No independent finite comparison
character is chosen here. -/
theorem commonEulerCompatibleSystem_endpoint_trace
    (m : ℕ) (𝒞 : SmoothProperEulerFamily N m)
    (R : CommonRealEulerQuotientRealization N m 𝒞)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    (hN : N.Prime) (h5 : 5 ≤ N) (hm : 0 < m) (hmN : m < N)
    (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (hξ : P.GoodUnit
      (algebraMap (realCyclotomicField N) (cyclotomicField N) ξ.val))
    (q : HeightOneSpectrum (𝓞 (realCyclotomicField N)))
    (hq : q ∉ (commonEulerCompatibleSystem N m 𝒞 R ξ hN h5 hm hmN).bad)
    [P.asIdeal.LiesOver q.asIdeal]
    (w : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    (hℓq : ((commonEulerCompatibleSystem N m 𝒞 R ξ hN h5 hm hmN).residueCharacteristic w :
      𝓞 (realCyclotomicField N)) ∉ q.asIdeal)
    (ι : Qbar →+* AlgebraicClosure (w.adicCompletion (cyclotomicField N)))
    (hι : ι.comp (cyclotomicField N).val.toRingHom =
      (algebraMap (w.adicCompletion (cyclotomicField N))
        (AlgebraicClosure (w.adicCompletion (cyclotomicField N)))).comp
        (algebraMap (cyclotomicField N) (w.adicCompletion (cyclotomicField N))))
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField N))))
    [Q.IsMaximal] [Q.LiesOver q.asIdeal] [Q.LiesOver P.asIdeal] :
    ι ((cyclotomicField N).val
      (normalizedCyclotomicEulerTrace N P.asIdeal hP m
        (P.specialization
          (algebraMap (realCyclotomicField N) (cyclotomicField N) ξ.val)
          hξ.valuation_eq_one.le))) =
    algebraMap (w.adicCompletion (cyclotomicField N))
      (AlgebraicClosure (w.adicCompletion (cyclotomicField N)))
      (LinearMap.trace (w.adicCompletion (cyclotomicField N))
        (Fin 2 → w.adicCompletion (cyclotomicField N))
        ((commonEulerCompatibleSystem N m 𝒞 R ξ hN h5 hm hmN).action w
          (AlgEquiv.restrictScalarsHom (realCyclotomicField N)
            (NumberField.geometricFrobenius (cyclotomicField N)
              (AlgebraicClosure (realCyclotomicField N)) P.asIdeal Q :
                AlgebraicClosure (realCyclotomicField N) ≃ₐ[cyclotomicField N]
                  AlgebraicClosure (realCyclotomicField N))))) := by
  let t := normalizedCyclotomicEulerTrace N P.asIdeal hP m
    (P.specialization
      (algebraMap (realCyclotomicField N) (cyclotomicField N) ξ.val)
      hξ.valuation_eq_one.le)
  have hreal : realEulerParameter N ξ =
      algebraMap (realCyclotomicField N) (cyclotomicField N) ξ.val :=
    realEulerParameter_eq_algebraMap N ξ
  have hξ' : P.GoodUnit (realEulerParameter N ξ) := by
    rwa [hreal]
  have hℓq' : (NumberField.primeBelow (cyclotomicField N) w :
      𝓞 (realCyclotomicField N)) ∉ q.asIdeal := by
    simpa only [commonEulerCompatibleSystem_residueCharacteristic] using hℓq
  have ht := commonEulerCompatibleSystem_geometricFrobenius_trace
    N m 𝒞 R ξ hN h5 hm hmN w q hq hℓq' P hP hξ' Q
  simp only [realEulerParameter_eq_algebraMap] at ht
  have hcoeff := congrArg
    (fun f : cyclotomicField N →+*
      AlgebraicClosure (w.adicCompletion (cyclotomicField N)) => f t) hι
  change ι ((cyclotomicField N).val t) =
    algebraMap (w.adicCompletion (cyclotomicField N))
      (AlgebraicClosure (w.adicCompletion (cyclotomicField N)))
      (algebraMap (cyclotomicField N)
        (w.adicCompletion (cyclotomicField N)) t) at hcoeff
  exact hcoeff.trans (congrArg _ ht.symm)

end HilbertModularity.Hypergeometric
