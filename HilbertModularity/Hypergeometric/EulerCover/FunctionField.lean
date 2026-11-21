/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.EulerCover.Integrality
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.Etale.Field

/-! # Function field of the affine Euler cover

The fraction field of the actual affine Euler root algebra is the generic
function field of the cover in [TripathiGoswamiRevised, Definition 2.3].
-/

@[expose] public noncomputable section

open Polynomial
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace HilbertModularity.Hypergeometric.EulerCover

variable {K : Type*} [Field K]

/-- The fraction field of the actual branch-open Euler-cover algebra. -/
abbrev CoverFunctionField (N m : ℕ) (t : K) := FractionRing (CoverRing N m t)

/-- The covering coordinate as an element of the actual function field. -/
def coverFunctionFieldRoot (N m : ℕ) (t : K) : CoverFunctionField N m t :=
  algebraMap (CoverRing N m t) (CoverFunctionField N m t) (coverRoot N m t)

/-- The base coordinate as an element of the actual function field. -/
def coverFunctionFieldX (N m : ℕ) (t : K) : CoverFunctionField N m t :=
  algebraMap K[X] (CoverFunctionField N m t) X

private theorem branchProduct_ne_zero (t : K) : branchProduct t ≠ 0 := by
  have hc : (branchProduct t).coeff 1 = 1 := by
    rw [branchProduct, mul_assoc, coeff_X_mul]
    simp [coeff_zero_eq_eval_zero]
  intro h
  rw [h] at hc
  have hzero : (1 : K) = 0 := by simpa using hc.symm
  exact one_ne_zero hzero

/-- The coordinate ring of the branch complement remains a domain. -/
theorem baseRing_isDomain (t : K) : IsDomain (BaseRing t) :=
  Localization.Away.isDomain (branchProduct_ne_zero t)

instance (t : K) : IsDomain (BaseRing t) := baseRing_isDomain t

/-- The branch-complement localization embeds the polynomial coordinate ring. -/
theorem polynomial_to_baseRing_injective (t : K) :
    Function.Injective (algebraMap K[X] (BaseRing t)) := by
  apply IsLocalization.injective (M := Submonoid.powers (branchProduct t))
    (BaseRing t)
  intro q hq
  obtain ⟨n, rfl⟩ := hq
  exact mem_nonZeroDivisors_iff_ne_zero.mpr
    (pow_ne_zero n (branchProduct_ne_zero t))

/-- The monic root-algebra presentation embeds the branch-complement ring. -/
theorem baseRing_to_coverRing_injective (N m : ℕ) (t : K) (hN : N ≠ 0) :
    Function.Injective (algebraMap (BaseRing t) (CoverRing N m t)) := by
  have hpos : 0 < N := Nat.pos_of_ne_zero hN
  have hdegree : 0 < (coverPolynomial N m t).degree := by
    rw [coverPolynomial, degree_X_pow_sub_C hpos]
    exact_mod_cast hpos
  have : FaithfulSMul (BaseRing t) (CoverRing N m t) :=
    AdjoinRoot.faithfulSMul_of_monic_of_degree_pos
      (coverPolynomial_monic N m t hN) hdegree
  exact FaithfulSMul.algebraMap_injective (BaseRing t) (CoverRing N m t)

/-- The generic coordinate field of the branch complement. It is canonically K(x). -/
abbrev BaseFunctionField (t : K) := FractionRing (BaseRing t)

/-- The generic coordinate field of the branch complement is the rational
function field of the original polynomial coordinate. -/
noncomputable def rationalFunctionEquivBaseFunctionField (t : K) :
    FractionRing K[X] ≃ₐ[K[X]] BaseFunctionField t := by
  letI : IsLocalization
      (Submonoid.comap (algebraMap K[X] (BaseRing t))
        (nonZeroDivisors (BaseRing t))) (BaseFunctionField t) :=
    IsLocalization.localization_localization_isLocalization_of_has_all_units
      (Submonoid.powers (branchProduct t))
      (nonZeroDivisors (BaseRing t)) (BaseFunctionField t)
      (by
        intro b hb
        exact mem_nonZeroDivisors_iff_ne_zero.mpr hb.ne_zero)
  have hle : Submonoid.comap (algebraMap K[X] (BaseRing t))
      (nonZeroDivisors (BaseRing t)) ≤ nonZeroDivisors K[X] := by
    intro p hp
    change algebraMap K[X] (BaseRing t) p ∈ nonZeroDivisors (BaseRing t) at hp
    rw [mem_nonZeroDivisors_iff_ne_zero] at hp ⊢
    intro h
    apply hp
    simp [h]
  letI : IsFractionRing K[X] (BaseFunctionField t) :=
    IsLocalization.of_le
      (Submonoid.comap (algebraMap K[X] (BaseRing t))
        (nonZeroDivisors (BaseRing t))) (nonZeroDivisors K[X]) hle (by
      intro p hp
      have hB : algebraMap K[X] (BaseRing t) p ≠ 0 := by
        intro h
        apply mem_nonZeroDivisors_iff_ne_zero.mp hp
        apply polynomial_to_baseRing_injective t
        simpa using h
      have hF : algebraMap (BaseRing t) (BaseFunctionField t)
          (algebraMap K[X] (BaseRing t) p) ≠ 0 := by
        intro h
        apply hB
        apply IsFractionRing.injective (BaseRing t) (BaseFunctionField t)
        simpa using h
      have hF' : algebraMap K[X] (BaseFunctionField t) p ≠ 0 := by
        rw [IsScalarTower.algebraMap_apply K[X] (BaseRing t)
          (BaseFunctionField t)]
        exact hF
      exact hF'.isUnit)
  exact IsLocalization.algEquiv (nonZeroDivisors K[X])
    (FractionRing K[X]) (BaseFunctionField t)

/-- The natural embedding of the generic base field into the actual Euler function field. -/
def baseFunctionFieldToCoverFunctionField (N m : ℕ) (t : K) (hN : N ≠ 0)
    (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N) :
    BaseFunctionField t →+* CoverFunctionField N m t := by
  letI : IsDomain (CoverRing N m t) := coverRing_isDomain N m t hN hmPos hm hcop
  apply IsFractionRing.lift
    (g := algebraMap (BaseRing t) (CoverFunctionField N m t))
  exact (IsFractionRing.injective (CoverRing N m t) (CoverFunctionField N m t)).comp
    (baseRing_to_coverRing_injective N m t hN)

/-- The generic base-field embedding sends a base element to its actual image in the
fraction field of the cover. -/
theorem baseFunctionFieldToCoverFunctionField_algebraMap (N m : ℕ) (t : K)
    (hN : N ≠ 0) (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N)
    (b : BaseRing t) :
    baseFunctionFieldToCoverFunctionField N m t hN hmPos hm hcop
      (algebraMap (BaseRing t) (BaseFunctionField t) b) =
      algebraMap (BaseRing t) (CoverFunctionField N m t) b := by
  let : IsDomain (CoverRing N m t) := coverRing_isDomain N m t hN hmPos hm hcop
  exact IsFractionRing.lift_algebraMap _ _

/-- The generic base-field map sends the polynomial coordinate to the actual
base coordinate in the Euler function field. -/
theorem baseFunctionFieldToCoverFunctionField_X (N m : ℕ) (t : K)
    (hN : N ≠ 0) (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N) :
    baseFunctionFieldToCoverFunctionField N m t hN hmPos hm hcop
      (algebraMap (BaseRing t) (BaseFunctionField t)
        (algebraMap K[X] (BaseRing t) X)) =
      coverFunctionFieldX N m t := by
  rw [baseFunctionFieldToCoverFunctionField_algebraMap]
  exact (IsScalarTower.algebraMap_apply K[X] (BaseRing t)
    (CoverFunctionField N m t) X).symm

/-- The generic fibre of the actual branch-open Euler-cover algebra. -/
abbrev GenericCoverRing (N m : ℕ) (t : K) :=
  BaseFunctionField t ⊗[BaseRing t] CoverRing N m t

/-- The generic Euler-cover algebra is a domain, as the localization of the actual
integral affine cover at the nonzero elements of its base. -/
theorem genericCoverRing_isDomain (N m : ℕ) (t : K) (hN : N ≠ 0)
    (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N) :
    IsDomain (GenericCoverRing N m t) := by
  let : IsDomain (CoverRing N m t) := coverRing_isDomain N m t hN hmPos hm hcop
  let : IsLocalization
      (Algebra.algebraMapSubmonoid (CoverRing N m t) (nonZeroDivisors (BaseRing t)))
      (GenericCoverRing N m t) :=
    IsLocalization.tensorRight (BaseFunctionField t) (nonZeroDivisors (BaseRing t))
  apply IsLocalization.isDomain_of_le_nonZeroDivisors
    (R := CoverRing N m t)
    (M := Algebra.algebraMapSubmonoid (CoverRing N m t) (nonZeroDivisors (BaseRing t)))
    (GenericCoverRing N m t)
  intro a ha
  obtain ⟨b, hb, rfl⟩ := Submonoid.mem_map.mp ha
  rw [mem_nonZeroDivisors_iff_ne_zero]
  intro h
  apply mem_nonZeroDivisors_iff_ne_zero.mp hb
  apply baseRing_to_coverRing_injective N m t hN
  simpa using h

/-- The generic Euler-cover algebra is finite over its base function field. -/
theorem genericCoverRing_finite (N m : ℕ) (t : K) (hN : N ≠ 0) :
    Module.Finite (BaseFunctionField t) (GenericCoverRing N m t) := by
  let b := (AdjoinRoot.powerBasis' (coverPolynomial_monic N m t hN)).basis
  exact Module.Finite.of_basis (b.baseChange (BaseFunctionField t))

/-- The generic fibre has the exact monic-presentation degree. -/
theorem genericCoverRing_finrank (N m : ℕ) (t : K) (hN : N ≠ 0) :
    Module.finrank (BaseFunctionField t) (GenericCoverRing N m t) = N := by
  let : Module.Free (BaseRing t) (CoverRing N m t) := coverRing_free N m t hN
  rw [Module.finrank_baseChange]
  rw [(AdjoinRoot.powerBasis' (coverPolynomial_monic N m t hN)).finrank]
  exact natDegree_X_pow_sub_C

/-- A finite-dimensional generic fibre of the integral Euler cover is a field. -/
theorem genericCoverRing_isField (N m : ℕ) (t : K) (hN : N ≠ 0)
    (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N) :
    IsField (GenericCoverRing N m t) := by
  let : IsDomain (GenericCoverRing N m t) :=
    genericCoverRing_isDomain N m t hN hmPos hm hcop
  let : Module.Finite (BaseFunctionField t) (GenericCoverRing N m t) :=
    genericCoverRing_finite N m t hN
  let : IsArtinianRing (GenericCoverRing N m t) :=
    IsArtinianRing.of_finite (BaseFunctionField t) (GenericCoverRing N m t)
  exact IsArtinianRing.isField_of_isDomain (GenericCoverRing N m t)

/-- The localized actual Euler algebra is canonically the fraction field of the
cover algebra. The equivalence is over the cover algebra itself. -/
noncomputable def genericCoverRingEquivFunctionField (N m : ℕ) (t : K) (hN : N ≠ 0)
    (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N) :
    GenericCoverRing N m t ≃ₐ[CoverRing N m t] CoverFunctionField N m t := by
  letI : IsDomain (CoverRing N m t) := coverRing_isDomain N m t hN hmPos hm hcop
  letI : IsLocalization
      (Algebra.algebraMapSubmonoid (CoverRing N m t) (nonZeroDivisors (BaseRing t)))
      (GenericCoverRing N m t) :=
    IsLocalization.tensorRight (BaseFunctionField t) (nonZeroDivisors (BaseRing t))
  have hM : Algebra.algebraMapSubmonoid (CoverRing N m t)
      (nonZeroDivisors (BaseRing t)) ≤ nonZeroDivisors (CoverRing N m t) := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := Submonoid.mem_map.mp ha
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro h
    apply mem_nonZeroDivisors_iff_ne_zero.mp hb
    apply baseRing_to_coverRing_injective N m t hN
    simpa using h
  letI : Field (GenericCoverRing N m t) :=
    (genericCoverRing_isField N m t hN hmPos hm hcop).toField
  have hinj : Function.Injective
      (algebraMap (CoverRing N m t) (GenericCoverRing N m t)) :=
    IsLocalization.injective (GenericCoverRing N m t) hM
  letI : FaithfulSMul (CoverRing N m t) (GenericCoverRing N m t) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  letI : IsFractionRing (CoverRing N m t) (GenericCoverRing N m t) :=
    IsLocalization.of_le
      (Algebra.algebraMapSubmonoid (CoverRing N m t) (nonZeroDivisors (BaseRing t)))
      (nonZeroDivisors (CoverRing N m t)) hM (by
      intro a ha
      have hn : algebraMap (CoverRing N m t) (GenericCoverRing N m t) a ≠ 0 := by
        intro h
        apply mem_nonZeroDivisors_iff_ne_zero.mp ha
        apply hinj
        simpa using h
      exact hn.isUnit)
  exact IsLocalization.algEquiv (nonZeroDivisors (CoverRing N m t))
    (GenericCoverRing N m t) (CoverFunctionField N m t)

/-- The generic-fibre equivalence sends the actual covering coordinate to its
image in the fraction field. -/
theorem genericCoverRingEquivFunctionField_coverRoot (N m : ℕ) (t : K)
    (hN : N ≠ 0) (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N) :
    genericCoverRingEquivFunctionField N m t hN hmPos hm hcop
      (algebraMap (CoverRing N m t) (GenericCoverRing N m t) (coverRoot N m t)) =
      coverFunctionFieldRoot N m t :=
  (genericCoverRingEquivFunctionField N m t hN hmPos hm hcop).commutes _

/-- The actual base-field inclusion gives the Euler function field its natural
structure over the generic coordinate field. -/
@[instance_reducible]
noncomputable def coverFunctionFieldAlgebra (N m : ℕ) (t : K) (hN : N ≠ 0)
    (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N) :
    Algebra (BaseFunctionField t) (CoverFunctionField N m t) :=
  (baseFunctionFieldToCoverFunctionField N m t hN hmPos hm hcop).toAlgebra

/-- The generic-fibre equivalence also respects the actual base function field. -/
theorem genericCoverRingEquivFunctionField_baseFunctionField (N m : ℕ) (t : K)
    (hN : N ≠ 0) (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N)
    (b : BaseFunctionField t) :
    genericCoverRingEquivFunctionField N m t hN hmPos hm hcop
      (algebraMap (BaseFunctionField t) (GenericCoverRing N m t) b) =
      baseFunctionFieldToCoverFunctionField N m t hN hmPos hm hcop b := by
  let : IsDomain (CoverRing N m t) := coverRing_isDomain N m t hN hmPos hm hcop
  let e := genericCoverRingEquivFunctionField N m t hN hmPos hm hcop
  have heq : e.toRingHom.comp (algebraMap (BaseFunctionField t) (GenericCoverRing N m t)) =
      baseFunctionFieldToCoverFunctionField N m t hN hmPos hm hcop := by
    apply IsFractionRing.ringHom_ext (A := BaseRing t)
    intro a
    change e (algebraMap (BaseFunctionField t) (GenericCoverRing N m t)
      (algebraMap (BaseRing t) (BaseFunctionField t) a)) = _
    rw [baseFunctionFieldToCoverFunctionField_algebraMap]
    have hbase :
        (algebraMap (BaseFunctionField t) (GenericCoverRing N m t))
          ((algebraMap (BaseRing t) (BaseFunctionField t)) a) =
        (algebraMap (CoverRing N m t) (GenericCoverRing N m t))
          ((algebraMap (BaseRing t) (CoverRing N m t)) a) := by
      calc
        _ = algebraMap (BaseRing t) (GenericCoverRing N m t) a :=
          (Algebra.TensorProduct.algebraMap_apply a).symm
        _ = 1 ⊗ₜ[BaseRing t] algebraMap (BaseRing t) (CoverRing N m t) a :=
          Algebra.TensorProduct.algebraMap_apply' a
        _ = _ := (Algebra.TensorProduct.right_algebraMap_apply _).symm
    rw [hbase]
    exact e.commutes (algebraMap (BaseRing t) (CoverRing N m t) a)
  exact RingHom.congr_fun heq b

/-- The generic fibre and the actual fraction field are equivalent over the
generic coordinate field, preserving both structural maps. -/
noncomputable def genericCoverRingEquivFunctionFieldOverBase (N m : ℕ) (t : K)
    (hN : N ≠ 0) (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N) :
    letI := coverFunctionFieldAlgebra N m t hN hmPos hm hcop
    GenericCoverRing N m t ≃ₐ[BaseFunctionField t] CoverFunctionField N m t := by
  letI := coverFunctionFieldAlgebra N m t hN hmPos hm hcop
  exact AlgEquiv.ofRingEquiv (fun b =>
    genericCoverRingEquivFunctionField_baseFunctionField N m t hN hmPos hm hcop b)

/-- The generic-fibre equivalence sends the base coordinate to its actual
image in the fraction field. -/
theorem genericCoverRingEquivFunctionField_baseX (N m : ℕ) (t : K)
    (hN : N ≠ 0) (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N) :
    genericCoverRingEquivFunctionField N m t hN hmPos hm hcop
      (algebraMap (CoverRing N m t) (GenericCoverRing N m t)
        (algebraMap K[X] (CoverRing N m t) X)) =
      coverFunctionFieldX N m t := by
  let e := genericCoverRingEquivFunctionField N m t hN hmPos hm hcop
  change e (algebraMap (CoverRing N m t) (GenericCoverRing N m t)
    (algebraMap K[X] (CoverRing N m t) X)) =
    algebraMap K[X] (CoverFunctionField N m t) X
  rw [e.commutes]
  exact (IsScalarTower.algebraMap_apply K[X] (CoverRing N m t)
    (CoverFunctionField N m t) X).symm

/-- As a generic-coordinate-field extension, the actual Euler function field
has degree precisely the covering degree. -/
theorem coverFunctionField_finrank (N m : ℕ) (t : K) (hN : N ≠ 0)
    (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N) :
    letI := coverFunctionFieldAlgebra N m t hN hmPos hm hcop
    Module.finrank (BaseFunctionField t) (CoverFunctionField N m t) = N := by
  let := coverFunctionFieldAlgebra N m t hN hmPos hm hcop
  let e' := genericCoverRingEquivFunctionFieldOverBase N m t hN hmPos hm hcop
  rw [← e'.toLinearEquiv.finrank_eq]
  exact genericCoverRing_finrank N m t hN

/-- The generic fibre remains étale after passage to the base function field. -/
theorem genericCoverRing_etale (N m : ℕ) (t : K) (hN : N ≠ 0)
    (hNchar : (N : K) ≠ 0) :
    Algebra.Etale (BaseFunctionField t) (GenericCoverRing N m t) := by
  have : Algebra.Etale (BaseRing t) (CoverRing N m t) :=
    coverRing_etale N m t hN (isUnit_iff_ne_zero.mpr hNchar)
  infer_instance

/-- If the covering degree is nonzero in the coefficient field, the generic
Euler function-field extension is separable. -/
theorem coverFunctionField_isSeparable (N m : ℕ) (t : K) (hN : N ≠ 0)
    (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N)
    (hNchar : (N : K) ≠ 0) :
    letI := coverFunctionFieldAlgebra N m t hN hmPos hm hcop
    Algebra.IsSeparable (BaseFunctionField t) (CoverFunctionField N m t) := by
  let := coverFunctionFieldAlgebra N m t hN hmPos hm hcop
  let : Field (GenericCoverRing N m t) :=
    (genericCoverRing_isField N m t hN hmPos hm hcop).toField
  have : Algebra.Etale (BaseFunctionField t) (GenericCoverRing N m t) :=
    genericCoverRing_etale N m t hN hNchar
  have : Algebra.IsSeparable (BaseFunctionField t) (GenericCoverRing N m t) :=
    (Algebra.FormallyEtale.iff_isSeparable _ _).mp inferInstance
  let e' := genericCoverRingEquivFunctionFieldOverBase N m t hN hmPos hm hcop
  exact (AlgEquiv.Algebra.isSeparable_iff e').mp inferInstance

/-- The normalized Kummer coordinate inside the actual Euler function field. -/
def coverFunctionFieldNormalizedRoot (N m : ℕ) (t : K) :
    CoverFunctionField N m t :=
  algebraMap (CoverRing N m t) (CoverFunctionField N m t) (normalizedRoot t N m)

/-- The deck action on the affine cover extends uniquely to its fraction field. -/
noncomputable def deckFunctionFieldAction (N m : ℕ) [NeZero N] (t : K)
    (ζ : rootsOfUnity N K) :
    CoverFunctionField N m t ≃ₐ[BaseRing t] CoverFunctionField N m t :=
  IsFractionRing.algEquivOfAlgEquiv (deckAlgebraAction N m t ζ)

/-- The extended deck action scales the actual covering coordinate. -/
theorem deckFunctionFieldAction_root (N m : ℕ) [NeZero N] (t : K)
    (ζ : rootsOfUnity N K) :
    deckFunctionFieldAction N m t ζ (coverFunctionFieldRoot N m t) =
      (algebraMap K[X] (BaseRing t) (C ((ζ : Kˣ) : K))) •
        coverFunctionFieldRoot N m t := by
  rw [coverFunctionFieldRoot, deckFunctionFieldAction,
    IsFractionRing.algEquivOfAlgEquiv_algebraMap, deckAlgebraAction_root]
  simp only [Algebra.smul_def, map_mul,
    IsScalarTower.algebraMap_apply (BaseRing t) (CoverRing N m t)
      (CoverFunctionField N m t)]

/-- Coprime exponent change extends from the actual affine covers to their
fraction fields. -/
noncomputable def exponentChangeFunctionFieldEquiv (N m mprime k : ℕ) (t : K)
    (hm : m < N) (hbezout : m * mprime = 1 + k * N) :
    CoverFunctionField N m t ≃ₐ[BaseRing t] CoverFunctionField N 1 t :=
  IsFractionRing.algEquivOfAlgEquiv
    (exponentChangeEquiv t N m mprime k hm hbezout)

/-- In the function fields, the normalized coordinate `z_m` maps to `z_1^m`. -/
theorem exponentChangeFunctionFieldEquiv_normalizedRoot (N m mprime k : ℕ)
    (t : K) (hm : m < N) (hbezout : m * mprime = 1 + k * N) :
    exponentChangeFunctionFieldEquiv N m mprime k t hm hbezout
      (coverFunctionFieldNormalizedRoot N m t) =
        coverFunctionFieldNormalizedRoot N 1 t ^ m := by
  simp only [coverFunctionFieldNormalizedRoot, exponentChangeFunctionFieldEquiv,
    IsFractionRing.algEquivOfAlgEquiv_algebraMap,
    exponentChangeEquiv_normalizedRoot, map_pow]

/-- In the function fields, the original Euler coordinate maps to
`(1-x) z_1^m`. -/
theorem exponentChangeFunctionFieldEquiv_root (N m mprime k : ℕ) (t : K)
    (hm : m < N) (hbezout : m * mprime = 1 + k * N) :
    exponentChangeFunctionFieldEquiv N m mprime k t hm hbezout
      (coverFunctionFieldRoot N m t) =
      algebraMap (BaseRing t) (CoverFunctionField N 1 t)
        (oneMinusXUnit t : BaseRing t) *
        coverFunctionFieldNormalizedRoot N 1 t ^ m := by
  rw [coverFunctionFieldRoot, exponentChangeFunctionFieldEquiv,
    IsFractionRing.algEquivOfAlgEquiv_algebraMap,
    exponentChangeEquiv_coverRoot, map_mul, map_pow]
  rw [IsScalarTower.algebraMap_apply (BaseRing t) (CoverRing N 1 t)
    (CoverFunctionField N 1 t)]
  rfl

private theorem functionFieldEquiv_baseFunctionField (N m₁ m₂ : ℕ) (t : K)
    (hN : N ≠ 0) (hm₁Pos : 1 ≤ m₁) (hm₁ : m₁ < N) (hcop₁ : m₁.Coprime N)
    (hm₂Pos : 1 ≤ m₂) (hm₂ : m₂ < N) (hcop₂ : m₂.Coprime N)
    (e : CoverFunctionField N m₁ t ≃ₐ[BaseRing t] CoverFunctionField N m₂ t)
    (b : BaseFunctionField t) :
    e (baseFunctionFieldToCoverFunctionField N m₁ t hN hm₁Pos hm₁ hcop₁ b) =
      baseFunctionFieldToCoverFunctionField N m₂ t hN hm₂Pos hm₂ hcop₂ b := by
  let : IsDomain (CoverRing N m₂ t) :=
    coverRing_isDomain N m₂ t hN hm₂Pos hm₂ hcop₂
  have heq : e.toRingHom.comp
      (baseFunctionFieldToCoverFunctionField N m₁ t hN hm₁Pos hm₁ hcop₁) =
      baseFunctionFieldToCoverFunctionField N m₂ t hN hm₂Pos hm₂ hcop₂ := by
    apply IsFractionRing.ringHom_ext (A := BaseRing t)
    intro a
    simp only [RingHom.comp_apply,
      baseFunctionFieldToCoverFunctionField_algebraMap]
    exact e.commutes a
  exact RingHom.congr_fun heq b

/-- The extended deck action fixes the whole rational-function base field. -/
theorem deckFunctionFieldAction_baseFunctionField (N m : ℕ) [NeZero N]
    (t : K) (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N)
    (ζ : rootsOfUnity N K) (b : BaseFunctionField t) :
    deckFunctionFieldAction N m t ζ
      (baseFunctionFieldToCoverFunctionField N m t (NeZero.ne N)
        hmPos hm hcop b) =
      baseFunctionFieldToCoverFunctionField N m t (NeZero.ne N)
        hmPos hm hcop b :=
  functionFieldEquiv_baseFunctionField N m m t (NeZero.ne N)
    hmPos hm hcop hmPos hm hcop (deckFunctionFieldAction N m t ζ) b

/-- Deck transformations fix the base coordinate in the actual function field. -/
theorem deckFunctionFieldAction_X (N m : ℕ) [NeZero N] (t : K)
    (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N)
    (ζ : rootsOfUnity N K) :
    deckFunctionFieldAction N m t ζ (coverFunctionFieldX N m t) =
      coverFunctionFieldX N m t := by
  have hb := deckFunctionFieldAction_baseFunctionField N m t hmPos hm hcop ζ
    (algebraMap (BaseRing t) (BaseFunctionField t)
      (algebraMap K[X] (BaseRing t) X))
  simpa only [baseFunctionFieldToCoverFunctionField_X] using hb

/-- The deck action is an automorphism over the actual rational-function base. -/
noncomputable def deckFunctionFieldActionOverBase (N m : ℕ) [NeZero N]
    (t : K) (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N)
    (ζ : rootsOfUnity N K) :
    letI := coverFunctionFieldAlgebra N m t (NeZero.ne N) hmPos hm hcop
    CoverFunctionField N m t ≃ₐ[BaseFunctionField t] CoverFunctionField N m t := by
  letI := coverFunctionFieldAlgebra N m t (NeZero.ne N) hmPos hm hcop
  let e := deckFunctionFieldAction N m t ζ
  exact AlgEquiv.ofRingEquiv (f := e.toRingEquiv)
    (deckFunctionFieldAction_baseFunctionField N m t hmPos hm hcop ζ)

/-- Coprime exponent change fixes the rational-function base field. -/
theorem exponentChangeFunctionFieldEquiv_baseFunctionField (N m mprime k : ℕ)
    (t : K) (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N)
    (hbezout : m * mprime = 1 + k * N) (b : BaseFunctionField t) :
    exponentChangeFunctionFieldEquiv N m mprime k t hm hbezout
      (baseFunctionFieldToCoverFunctionField N m t (by omega)
        hmPos hm hcop b) =
      baseFunctionFieldToCoverFunctionField N 1 t (by omega)
        (by omega) (by omega) (by simp) b := by
  have hN : N ≠ 0 := by omega
  have hOne : 1 < N := lt_of_le_of_lt hmPos hm
  exact functionFieldEquiv_baseFunctionField N m 1 t hN hmPos hm hcop
    (by omega) hOne (by simp)
    (exponentChangeFunctionFieldEquiv N m mprime k t hm hbezout) b

/-- Coprime exponent change fixes the actual base coordinate. -/
theorem exponentChangeFunctionFieldEquiv_X (N m mprime k : ℕ) (t : K)
    (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N)
    (hbezout : m * mprime = 1 + k * N) :
    exponentChangeFunctionFieldEquiv N m mprime k t hm hbezout
      (coverFunctionFieldX N m t) = coverFunctionFieldX N 1 t := by
  have hb := exponentChangeFunctionFieldEquiv_baseFunctionField N m mprime k t
    hmPos hm hcop hbezout
    (algebraMap (BaseRing t) (BaseFunctionField t)
      (algebraMap K[X] (BaseRing t) X))
  simpa only [baseFunctionFieldToCoverFunctionField_X] using hb

/-- Coprime exponent change is an equivalence of the actual Euler function
fields over their common rational-function base. -/
noncomputable def exponentChangeFunctionFieldEquivOverBase (N m mprime k : ℕ)
    (t : K) (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N)
    (hbezout : m * mprime = 1 + k * N) :
    letI := coverFunctionFieldAlgebra N m t (by omega) hmPos hm hcop
    letI := coverFunctionFieldAlgebra N 1 t (by omega)
      (by omega) (by omega) (by simp)
    CoverFunctionField N m t ≃ₐ[BaseFunctionField t]
      CoverFunctionField N 1 t := by
  have hN : N ≠ 0 := by omega
  have hOne : 1 < N := lt_of_le_of_lt hmPos hm
  letI := coverFunctionFieldAlgebra N m t hN hmPos hm hcop
  letI := coverFunctionFieldAlgebra N 1 t hN (by omega) hOne (by simp)
  let e := exponentChangeFunctionFieldEquiv N m mprime k t hm hbezout
  exact AlgEquiv.ofRingEquiv (f := e.toRingEquiv)
    (exponentChangeFunctionFieldEquiv_baseFunctionField N m mprime k t
      hmPos hm hcop hbezout)

/-- Coprime exponent change intertwines the actual deck actions on the
function fields. The `m`-cover parameter `ζ` becomes `ζ^mprime`. -/
theorem exponentChangeFunctionFieldEquiv_deck (N m mprime k : ℕ)
    [NeZero N] (t : K) (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N)
    (hbezout : m * mprime = 1 + k * N) (ζ : rootsOfUnity N K)
    (z : CoverFunctionField N m t) :
    exponentChangeFunctionFieldEquiv N m mprime k t hm hbezout
      (deckFunctionFieldAction N m t ζ z) =
      deckFunctionFieldAction N 1 t (ζ ^ mprime)
        (exponentChangeFunctionFieldEquiv N m mprime k t hm hbezout z) := by
  have hOne : 1 < N := lt_of_le_of_lt hmPos hm
  let : IsDomain (CoverRing N m t) :=
    coverRing_isDomain N m t (NeZero.ne N) hmPos hm hcop
  let : IsDomain (CoverRing N 1 t) :=
    coverRing_isDomain N 1 t (NeZero.ne N) (by omega) hOne (by simp)
  let e := exponentChangeFunctionFieldEquiv N m mprime k t hm hbezout
  let dm := deckFunctionFieldAction N m t ζ
  let d1 := deckFunctionFieldAction N 1 t (ζ ^ mprime)
  have hcomp : e.toRingHom.comp dm.toRingHom =
      d1.toRingHom.comp e.toRingHom := by
    apply IsFractionRing.ringHom_ext (A := CoverRing N m t)
    intro a
    change e (dm (algebraMap (CoverRing N m t) (CoverFunctionField N m t) a)) =
      d1 (e (algebraMap (CoverRing N m t) (CoverFunctionField N m t) a))
    simp only [e, dm, d1, deckFunctionFieldAction,
      exponentChangeFunctionFieldEquiv,
      IsFractionRing.algEquivOfAlgEquiv_algebraMap]
    have h := congrArg
      (fun f : CoverRing N m t →ₐ[BaseRing t] CoverRing N 1 t => f a)
      (exponentChangeEquiv_deck t N m mprime k hm hbezout ζ)
    exact congrArg (algebraMap (CoverRing N 1 t) (CoverFunctionField N 1 t)) h
  exact RingHom.congr_fun hcomp z

/-- Equivalently, base-cover deck parameter `ζ` acts by `ζ^m` on the
`m`-cover function field. -/
theorem exponentChangeFunctionFieldEquiv_deck_baseParameter (N m mprime k : ℕ)
    [NeZero N] (t : K) (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N)
    (hbezout : m * mprime = 1 + k * N) (ζ : rootsOfUnity N K)
    (z : CoverFunctionField N m t) :
    exponentChangeFunctionFieldEquiv N m mprime k t hm hbezout
      (deckFunctionFieldAction N m t (ζ ^ m) z) =
      deckFunctionFieldAction N 1 t ζ
        (exponentChangeFunctionFieldEquiv N m mprime k t hm hbezout z) := by
  simpa only [AdjoinRoot.rootsOfUnity_pow_bezout' N m mprime k hbezout] using
    exponentChangeFunctionFieldEquiv_deck N m mprime k t hmPos hm hcop
      hbezout (ζ ^ m) z

end HilbertModularity.Hypergeometric.EulerCover
