/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.GaloisRealizationClosure
public import HilbertModularity.Hypergeometric.ReflectionFrobeniusLift
public import HilbertModularity.Geometry.Etale.LocalSystem
public import Mathlib.FieldTheory.IntermediateField.Algebraic

/-! # The chosen real-field descent of the proper Euler system

The geometric fixed-character summand on the exponent-`m` curve is defined over
the full cyclotomic field.  The descent supplied by [GPRV, Theorem 9.2 and
Proposition 9.5] is chosen on the *generic family*, before specialization.
For odd `N`, the auxiliary `κ_N` of [GPRV, Definition 8.8] is trivial.
No trace identity is built into the descent input.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory
open HilbertModularity.Cyclotomic

namespace HilbertModularity.Hypergeometric

universe u

variable (N : ℕ) [NeZero N]

/-- The fixed real-to-cyclotomic coefficient map is the canonical
intermediate-field inclusion. -/
theorem realEulerCoefficientInclusion_eq :
    realEulerCoefficientInclusion N =
      IntermediateField.inclusion (realCyclotomicField_le N) :=
  (rfl)

/-- The real coefficient label inside the chosen cyclotomic field. -/
@[simp] theorem realEulerCoefficientInclusion_tau (m : ℕ) :
    realEulerCoefficientInclusion N (tau N m) =
      (root N) ^ m + (root N)⁻¹ ^ m := by
  apply Subtype.ext
  simp [realEulerCoefficientInclusion, tau, root]

/-- The same parameter viewed in the field over which the proper Euler curve
and its fixed deck projector were constructed. -/
def realEulerParameter (ξ : ProjectiveLine.Parameter (realCyclotomicField N)) :
    cyclotomicField N :=
  realEulerCoefficientInclusion N ξ.val

/-- The Euler parameter is the image of the original real parameter under
the fixed coefficient-field inclusion. -/
theorem realEulerParameter_eq_inclusion
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N)) :
    realEulerParameter N ξ = realEulerCoefficientInclusion N ξ.val :=
  (rfl)

theorem realEulerParameter_isUnit
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N)) :
    IsUnit (realEulerParameter N ξ) :=
  (isUnit_iff_ne_zero.mpr ξ.property.1).map (realEulerCoefficientInclusion N)

theorem one_sub_realEulerParameter_isUnit
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N)) :
    IsUnit (1 - realEulerParameter N ξ) := by
  have h : IsUnit (1 - ξ.val) :=
    isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr ξ.property.2.symm)
  change IsUnit (1 - realEulerCoefficientInclusion N ξ.val)
  simpa only [map_one, map_sub] using h.map (realEulerCoefficientInclusion N)

/-- A common closure for the real coefficient field, compatible with the
already fixed `Qbar` used for the proper Euler cohomology. -/
def realEulerClosureEquiv :
    AlgebraicClosure (realCyclotomicField N) ≃+* Qbar := by
  letI : IsAlgClosure (realCyclotomicField N) Qbar :=
    ⟨inferInstance, inferInstance⟩
  exact IsAlgClosure.equivOfEquiv (AlgebraicClosure (realCyclotomicField N)) Qbar
    (RingEquiv.refl (realCyclotomicField N))

/-- The fixed closure identification retains the real coefficient field. -/
theorem realEulerClosureEquiv_algebraMap (a : realCyclotomicField N) :
    realEulerClosureEquiv N
      (algebraMap (realCyclotomicField N)
        (AlgebraicClosure (realCyclotomicField N)) a) =
      algebraMap (realCyclotomicField N) Qbar a := by
  simp [realEulerClosureEquiv, IsAlgClosure.equivOfEquiv_algebraMap]

/-- Transport a `Qbar` automorphism over the real field to the algebraic
closure used by the étale fibre functor. -/
def realEulerClosureGaloisHom :
    (Qbar ≃ₐ[realCyclotomicField N] Qbar) →*
      (AlgebraicClosure (realCyclotomicField N) ≃ₐ[realCyclotomicField N]
        AlgebraicClosure (realCyclotomicField N)) where
  toFun g :=
    AlgEquiv.ofRingEquiv
      (f := ((realEulerClosureEquiv N).trans g.toRingEquiv).trans
        (realEulerClosureEquiv N).symm) (by
        intro a
        simp only [RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv]
        apply (realEulerClosureEquiv N).injective
        simp only [RingEquiv.apply_symm_apply, realEulerClosureEquiv,
          IsAlgClosure.equivOfEquiv_algebraMap, RingEquiv.refl_apply]
        exact g.commutes a)
  map_one' := by
    apply AlgEquiv.ext
    intro a
    simp [realEulerClosureEquiv]
  map_mul' g h := by
    apply AlgEquiv.ext
    intro a
    change (realEulerClosureEquiv N).symm
        (g (h (realEulerClosureEquiv N a))) =
      (realEulerClosureEquiv N).symm
        (g (realEulerClosureEquiv N
          ((realEulerClosureEquiv N).symm
            (h (realEulerClosureEquiv N a)))))
    rw [RingEquiv.apply_symm_apply]

/-- The transported real-field Galois action is literal conjugation by the
chosen closure identification. -/
theorem realEulerClosureGaloisHom_apply
    (g : Qbar ≃ₐ[realCyclotomicField N] Qbar)
    (a : AlgebraicClosure (realCyclotomicField N)) :
    realEulerClosureGaloisHom N g a =
      (realEulerClosureEquiv N).symm (g (realEulerClosureEquiv N a)) :=
  (rfl)

/-- Conjugation by the fixed closure equivalence is an equivalence of the two
absolute Galois groups. Its forward map is the homomorphism already used by
the selected Euler descent. -/
def realEulerClosureGaloisEquiv :
    (Qbar ≃ₐ[realCyclotomicField N] Qbar) ≃*
      (AlgebraicClosure (realCyclotomicField N) ≃ₐ[realCyclotomicField N]
        AlgebraicClosure (realCyclotomicField N)) where
  toFun := realEulerClosureGaloisHom N
  invFun g := AlgEquiv.ofRingEquiv
    (f := (((realEulerClosureEquiv N).symm.trans g.toRingEquiv).trans
      (realEulerClosureEquiv N))) (by
        intro a
        apply (realEulerClosureEquiv N).symm.injective
        simp only [RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv,
          RingEquiv.symm_apply_apply]
        have he : (realEulerClosureEquiv N).symm
            (algebraMap (realCyclotomicField N) Qbar a) =
            algebraMap (realCyclotomicField N)
              (AlgebraicClosure (realCyclotomicField N)) a := by
          apply (realEulerClosureEquiv N).injective
          rw [RingEquiv.apply_symm_apply, realEulerClosureEquiv_algebraMap]
        rw [he]
        exact g.commutes a)
  left_inv g := by
    apply AlgEquiv.ext
    intro a
    change (realEulerClosureEquiv N)
      ((realEulerClosureEquiv N).symm
        (g ((realEulerClosureEquiv N) ((realEulerClosureEquiv N).symm a)))) = g a
    simp
  right_inv g := by
    apply AlgEquiv.ext
    intro a
    change (realEulerClosureEquiv N).symm
      ((realEulerClosureEquiv N)
        (g ((realEulerClosureEquiv N).symm (realEulerClosureEquiv N a)))) = g a
    simp
  map_mul' := (realEulerClosureGaloisHom N).map_mul

/-- The equivalence's forward action is the chosen descent's Galois map. -/
@[simp] theorem realEulerClosureGaloisEquiv_apply
    (g : Qbar ≃ₐ[realCyclotomicField N] Qbar) :
    realEulerClosureGaloisEquiv N g = realEulerClosureGaloisHom N g :=
  (rfl)

/-- The proper cohomology and the one generic descended local system share a
specific intertwiner at every real rational parameter.  This records the
cohomological origin of the descent, without stipulating its Frobenius trace.
The projector on the exponent-`m` curve is the fixed `χ₀` projector. -/
structure ProperEulerRealDescent (m ℓ : ℕ) [Fact ℓ.Prime]
    (L : Type u) [Field L] [TopologicalSpace L] [Algebra ℚ_[ℓ] L]
    (ι : cyclotomicField N →+* L)
    (𝒞 : SmoothProperEulerFamily N m) where
  localSystem : Scheme.EtaleLocalSystem.{0,u,u} (realCyclotomicField N)
    (ProjectiveLine.punctured (realCyclotomicField N)) L
  rank_two : ∀ ξ : ProjectiveLine.Parameter (realCyclotomicField N),
    Module.finrank L
      (localSystem.toFunctor.obj
        (Scheme.etaleFiberPoint _ _ (ProjectiveLine.puncturedPoint _ ξ))) = 2
  properComparison : ∀ ξ : ProjectiveLine.Parameter (realCyclotomicField N),
    (localSystem.toFunctor.obj
        (Scheme.etaleFiberPoint _ _ (ProjectiveLine.puncturedPoint _ ξ))) ≃ₗ[L]
      (properPrimitiveGaloisSubrepresentation N m 𝒞
        (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
        (one_sub_realEulerParameter_isUnit N ξ) ℓ L ι).toSubmodule
  properComparison_intertwines :
    ∀ (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
      (g : Qbar ≃ₐ[cyclotomicField N] Qbar)
      (v : localSystem.toFunctor.obj
        (Scheme.etaleFiberPoint _ _ (ProjectiveLine.puncturedPoint _ ξ))),
      properComparison ξ
        ((localSystem.arithmeticRepresentation
            (ProjectiveLine.puncturedPoint _ ξ)).comp
          ((realEulerClosureGaloisHom N).comp
            (restrictCyclotomicGalois N)) g v) =
        properPrimitiveQbarGaloisRepresentation N m 𝒞
          (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
          (one_sub_realEulerParameter_isUnit N ξ) ℓ L ι g
          (properComparison ξ v)

/-- [GPRV, Theorem 9.2 and Proposition 9.5, pp. 40–41] construct the
raw quotient motive for the coprime symmetric datum. Lemma 8.5, p. 30,
gives `(Irr)` since the scaled exponents `m,-m,m-N` have gcd one with `N`.
The rank-two lisse descent restricts to fixed-`χ₀` proper Euler cohomology
over `F_N`. For even `N`, this RAW descent is not yet the effective
hypergeometric normalization: the separate character of [GPRV, Definition
8.8, Lemma 8.9 and Corollary 8.10] must be tensored to power `m`. No
Frobenius trace, automorphy or Tate twist is asserted here. -/
theorem exists_properEulerRealDescent_of_coprime (m ℓ : ℕ) [Fact ℓ.Prime]
    (L : Type u) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra ℚ_[ℓ] L] [ContinuousSMul ℚ_[ℓ] L]
    [FiniteDimensional ℚ_[ℓ] L]
    (ι : cyclotomicField N →+* L)
    (h3 : 3 ≤ N) (hm : 0 < m) (hmN : m < N)
    (hcop : m.Coprime N)
    (𝒞 : SmoothProperEulerFamily N m) :
    Nonempty (ProperEulerRealDescent N m ℓ L ι 𝒞) := by
  sorry

/-- At odd `N`, κ_N is trivial [GPRV, Definition 8.8 and the paragraph
after Lemma 9.3, p. 40], so the same raw descent is effective. -/
theorem exists_properEulerRealDescent_of_odd_coprime (m ℓ : ℕ) [Fact ℓ.Prime]
    (L : Type u) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra ℚ_[ℓ] L] [ContinuousSMul ℚ_[ℓ] L]
    [FiniteDimensional ℚ_[ℓ] L]
    (ι : cyclotomicField N →+* L)
    (h3 : 3 ≤ N) (_hOdd : Odd N) (hm : 0 < m) (hmN : m < N)
    (hcop : m.Coprime N)
    (𝒞 : SmoothProperEulerFamily N m) :
    Nonempty (ProperEulerRealDescent N m ℓ L ι 𝒞) :=
  exists_properEulerRealDescent_of_coprime N m ℓ L ι h3 hm hmN hcop 𝒞

/-- The prime-level descent is the specialization of the odd coprime
source interface at the same Euler family and coefficient map. -/
theorem exists_properEulerRealDescent (m ℓ : ℕ) [Fact ℓ.Prime]
    (L : Type u) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra ℚ_[ℓ] L] [ContinuousSMul ℚ_[ℓ] L]
    [FiniteDimensional ℚ_[ℓ] L]
    (ι : cyclotomicField N →+* L)
    (hN : N.Prime) (h5 : 5 ≤ N) (hm : 0 < m) (hmN : m < N)
    (𝒞 : SmoothProperEulerFamily N m) :
    Nonempty (ProperEulerRealDescent N m ℓ L ι 𝒞) := by
  have hOdd : Odd N := hN.odd_of_ne_two (by omega)
  have hcop : m.Coprime N :=
    (hN.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hm hmN)).symm
  exact exists_properEulerRealDescent_of_odd_coprime N m ℓ L ι
    (le_trans (by decide : 3 ≤ 5) h5) hOdd hm hmN hcop 𝒞

/-- Choose the odd coprime generic descent once, before all fibres. -/
def chosenProperEulerRealDescent_of_odd_coprime (m ℓ : ℕ) [Fact ℓ.Prime]
    (L : Type u) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra ℚ_[ℓ] L] [ContinuousSMul ℚ_[ℓ] L]
    [FiniteDimensional ℚ_[ℓ] L]
    (ι : cyclotomicField N →+* L)
    (h3 : 3 ≤ N) (hOdd : Odd N) (hm : 0 < m) (hmN : m < N)
    (hcop : m.Coprime N)
    (𝒞 : SmoothProperEulerFamily N m) :
    ProperEulerRealDescent N m ℓ L ι 𝒞 :=
  Classical.choice (exists_properEulerRealDescent_of_odd_coprime N m ℓ L ι
    h3 hOdd hm hmN hcop 𝒞)

/-- The generic descent is selected once; all specializations below refer
to this same chosen family. -/
def chosenProperEulerRealDescent (m ℓ : ℕ) [Fact ℓ.Prime]
    (L : Type u) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra ℚ_[ℓ] L] [ContinuousSMul ℚ_[ℓ] L]
    [FiniteDimensional ℚ_[ℓ] L]
    (ι : cyclotomicField N →+* L)
    (hN : N.Prime) (h5 : 5 ≤ N) (hm : 0 < m) (hmN : m < N)
    (𝒞 : SmoothProperEulerFamily N m) :
    ProperEulerRealDescent N m ℓ L ι 𝒞 :=
  Classical.choice (exists_properEulerRealDescent N m ℓ L ι hN h5 hm hmN 𝒞)

end HilbertModularity.Hypergeometric
