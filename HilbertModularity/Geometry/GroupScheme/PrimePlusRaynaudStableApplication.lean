/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.PrimePlusRaynaudPeriodMap
public import HilbertModularity.Geometry.GroupScheme.PrimePlusDeepCuspOrdinary
public import HilbertModularity.Hyperelliptic.SpecialFiberStableGeometry
public import HilbertModularity.Hyperelliptic.SpecialFiberGenericPlusModel
public import HilbertModularity.Hyperelliptic.SpecialFiberDeepCuspModel

/-! # Raynaud uniformization of the selected scaled plus Jacobian

The scaled integral double cover has two geometrically rational components,
`(p + 1) / 2` split nodes, and explicit local smoothing equations. The cited
semistable Picard and rigid uniformization theorems turn this geometry into a
period lattice and a split torus for the *same* pointed Jacobian. Node equations
of thickness greater than one are allowed; no regularity of the total space is
inferred from generic smoothness.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory HilbertModularity.Cyclotomic
  HilbertModularity.Hyperelliptic

namespace HilbertModularity.Hypergeometric

attribute [local instance] realPrimePowerCompletionPadicAlgebra
  realPrimePowerCompletionPadicTower realPrimePowerCompletion_uniformContinuousConstSMul
  realPrimePowerCompletionComplexTower primePlusDecompositionRationalModule
  primePlusDecompositionScalarTower primePlusConjugateRationalModule
  primePlusConjugateScalarTower

variable (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
  (ξ : ProjectiveLine.Parameter (realCyclotomicField p))

/-- The arithmetic output of the semistable Picard theorem and Raynaud's rigid
uniformization for the selected plus Jacobian. `M` is the integral period
lattice, `X₀` the character lattice of its split torus, and `Y` and `X` their
coefficient-field realizations. The valuation pairing remains explicit, as do
the Galois and real-multiplication actions on the covariant Tate module. -/
structure PrimePlusRaynaudUniformization where
  M : ModuleCat ℤ
  X₀ : ModuleCat ℤ
  MFinite : Module.Finite ℤ M
  X₀Finite : Module.Finite ℤ X₀
  MFree : Module.Free ℤ M
  X₀Free : Module.Free ℤ X₀
  Mrank : Module.finrank ℤ M = (p - 1) / 2
  X₀rank : Module.finrank ℤ X₀ = (p - 1) / 2
  Y : ModuleCat ℚ_[p]
  X : ModuleCat ℚ_[p]
  YRealModule : Module (RealPrimePowerCompletion p 0) Y
  YScalarTower : letI : Module (RealPrimePowerCompletion p 0) Y := YRealModule
    IsScalarTower ℚ_[p] (RealPrimePowerCompletion p 0) Y
  YFinite : Module.Finite ℚ_[p] Y
  Yrank : Module.finrank ℚ_[p] Y = (p - 1) / 2
  periodInclusion : M →ₗ[ℤ] Y
  characterInclusion : X₀ →ₗ[ℤ] X
  periodInclusion_injective : Function.Injective periodInclusion
  characterInclusion_injective : Function.Injective characterInclusion
  periodInclusion_spans : Submodule.span ℚ_[p] (Set.range periodInclusion) = ⊤
  characterInclusion_spans :
    Submodule.span ℚ_[p] (Set.range characterInclusion) = ⊤
  periodMap : letI : Module (RealPrimePowerCompletion p 0) Y := YRealModule
    primePlusDecompositionRepresentation p hp ξ →ₗ[RealPrimePowerCompletion p 0] Y
  periodMap_surjective : Function.Surjective periodMap
  periodAction : Representation ℤ
    Gal(PadicAlgCl p/RealPrimePowerCompletion p 0) M
  characterAction : Representation ℤ
    Gal(PadicAlgCl p/RealPrimePowerCompletion p 0) X₀
  YAction : Representation ℚ_[p]
    Gal(PadicAlgCl p/RealPrimePowerCompletion p 0) Y
  XAction : Representation ℚ_[p]
    Gal(PadicAlgCl p/RealPrimePowerCompletion p 0) X
  periodInclusion_equivariant : ∀ g m,
    periodInclusion (periodAction g m) = YAction g (periodInclusion m)
  characterInclusion_equivariant : ∀ g x,
    characterInclusion (characterAction g x) = XAction g (characterInclusion x)
  splitCharacterAction : ∀ g x, characterAction g x = x
  splitTorus : ∀ g x, XAction g x = x
  periodMap_equivariant : ∀ g v,
    periodMap ((primePlusDecompositionRepresentation p hp ξ).ρ g v) =
      YAction g (periodMap v)
  valuationPairing : M →ₗ[ℤ] X₀ →ₗ[ℤ] ℤ
  valuationPairing_nondegenerate : Function.Injective valuationPairing
  rationalPairing : Y →ₗ[ℚ_[p]] X →ₗ[ℚ_[p]] ℚ_[p]
  valuationPairing_compatible : ∀ m x,
    rationalPairing (periodInclusion m) (characterInclusion x) =
      (valuationPairing m x : ℚ_[p])
  rationalPairing_nondegenerate : Function.Injective rationalPairing
  rationalPairing_equivariant : ∀ g y x,
    rationalPairing (YAction g y) (XAction g x) = rationalPairing y x

/-- [SGA7I, Exposé IX, §§8.2 and 12.3; RaynaudRigid, §1 Theorem 1,
pp. 473–474, and §3(a)–(b), p. 475] Semistable Picard reduction and rigid
uniformization for the actual proper flat scaled cover. The hypothesis
`hgeometry` supplies its geometrically reduced connected special fibre, two
defined projective-line components, all rational split nodes and their local
equations, including the possible nonregular equations `xy = π^n`. The
punctured parameter has smooth connected generic fibre; `hJacobian` fixes the
same pointed Jacobian and its real-multiplication action. `hparameter` matches
the integral model's generic parameter to that fibre. The result asserts only
the cited period/torus construction and its functorial actions; the ordinary
quotient is deduced separately below. -/
theorem exists_primePlusRaynaudUniformization_of_scaledModel
    (T : (realPrimeAboveConductor p).valuationSubringAtPrime
      (realCyclotomicField p))
    (hgeometry : CyclotomicStableGeometry p T)
    (hparameter : (T : realCyclotomicField p) =
      ξ.val / (2 - tau p 1) ^ p)
    (hJacobian : Σ b : Over.mk (𝟙 (Spec
        (CommRingCat.of (realCyclotomicField p)))) ⟶
        Over.mk (scaledModelToSpec (realScaledRootPolynomial p)
          (ξ.val / (2 - tau p 1) ^ p)),
      GroupScheme.PointedCurveJacobian (realCyclotomicField p)
        (Over.mk (scaledModelToSpec (realScaledRootPolynomial p)
          (ξ.val / (2 - tau p 1) ^ p))) b
        (GroupScheme.fiber (realCyclotomicField p) (primePlusFamily p hp)
          (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ))) :
    Nonempty (PrimePlusRaynaudUniformization p hp ξ) := by
  sorry

/-- A split character action and an equivariant nondegenerate valuation
pairing force the rational period action to be trivial. This is the
manuscript's Galois deduction from Raynaud's pairing. -/
theorem PrimePlusRaynaudUniformization.YAction_fixed
    (D : PrimePlusRaynaudUniformization p hp ξ)
    (g : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0)) (y : D.Y) :
    D.YAction g y = y := by
  apply D.rationalPairing_nondegenerate
  apply LinearMap.ext
  intro x
  simpa only [D.splitTorus g x] using D.rationalPairing_equivariant g y x

/-- The actual integral period lattice has trivial Galois action: it embeds
equivariantly in the rational period realization, whose action is fixed by the
split torus pairing. -/
theorem PrimePlusRaynaudUniformization.periodAction_fixed
    (D : PrimePlusRaynaudUniformization p hp ξ)
    (g : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0)) (m : D.M) :
    D.periodAction g m = m := by
  apply D.periodInclusion_injective
  rw [D.periodInclusion_equivariant]
  exact D.YAction_fixed p hp ξ g (D.periodInclusion m)

/-- The specified Raynaud period map determines a weight-zero quotient at
every RM label, and that exact quotient has trivial Galois action. -/
theorem PrimePlusRaynaudUniformization.existsOrdinaryQuotientWithFixed
    (D : PrimePlusRaynaudUniformization p hp ξ)
    (m : ℕ) (hm : m.Coprime (p ^ (0 + 1))) :
    ∃ W : PrimePlusOrdinaryQuotient p hp ξ m hm,
      ∀ (g : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0))
        (v : (primePlusDecompositionScalarConjugate p hp ξ m hm) ⧸
          W.kernel.toSubmodule),
        (primePlusDecompositionScalarConjugate p hp ξ m hm).ρ.quotient
          W.kernel.toSubmodule W.kernel.apply_mem_toSubmodule g v = v := by
  let : Module (RealPrimePowerCompletion p 0) D.Y := D.YRealModule
  let : IsScalarTower ℚ_[p] (RealPrimePowerCompletion p 0) D.Y :=
    D.YScalarTower
  let : Module.Finite ℚ_[p] D.Y := D.YFinite
  have hfixed (g : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0))
      (v : primePlusDecompositionRepresentation p hp ξ) :
      D.periodMap ((primePlusDecompositionRepresentation p hp ξ).ρ g v) =
        D.periodMap v := by
    rw [D.periodMap_equivariant, D.YAction_fixed p hp ξ]
  exact exists_primePlusOrdinaryQuotient_of_RaynaudPeriodMap_with_fixed
    p hp ξ D.Y D.periodMap D.periodMap_surjective D.Yrank hfixed m hm

/-- The unlabelled native period quotient is retained for arithmetic
comparisons that twist the actual representation before choosing an RM label. -/
theorem PrimePlusRaynaudUniformization.existsBaseOrdinaryQuotientWithFixed
    (D : PrimePlusRaynaudUniformization p hp ξ) :
    ∃ W : HodgeTate.WeightZeroQuotient p
        (realPrimePowerLocalPeriodAction p 0)
        (realPrimePowerLocalPeriodAction_fixes p 0)
        (primePlusDecompositionRepresentation p hp ξ).ρ,
      ∀ (g : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0))
        (v : (primePlusDecompositionRepresentation p hp ξ) ⧸
          W.kernel.toSubmodule),
        (primePlusDecompositionRepresentation p hp ξ).ρ.quotient
          W.kernel.toSubmodule W.kernel.apply_mem_toSubmodule g v = v := by
  let : Module (RealPrimePowerCompletion p 0) D.Y := D.YRealModule
  let : IsScalarTower ℚ_[p] (RealPrimePowerCompletion p 0) D.Y :=
    D.YScalarTower
  let : Module.Finite ℚ_[p] D.Y := D.YFinite
  have hfixed (g : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0))
      (v : primePlusDecompositionRepresentation p hp ξ) :
      D.periodMap ((primePlusDecompositionRepresentation p hp ξ).ρ g v) =
        D.periodMap v := by
    rw [D.periodMap_equivariant, D.YAction_fixed p hp ξ]
  exact exists_primePlusBaseOrdinaryQuotient_of_RaynaudPeriodMap p hp ξ
    D.Y D.periodMap D.periodMap_surjective D.Yrank hfixed

/-- The normalized lower character of the *chosen Raynaud quotient* is one.
The quotient-character equivalence is carried by the same normalized basis,
so this conclusion is specific to the split period map. -/
theorem PrimePlusRaynaudUniformization.existsNormalizedOrdinaryDataLowerOne
    (D : PrimePlusRaynaudUniformization p hp ξ)
    (m : ℕ) (hm : m.Coprime (p ^ (0 + 1))) :
    ∃ d : PrimePlusNormalizedOrdinaryData p hp ξ m hm,
      d.lowerCharacter = 1 := by
  obtain ⟨W, hfixed⟩ := D.existsOrdinaryQuotientWithFixed p hp ξ m hm
  let d := W.normalizedData p hp ξ m hm
  refine ⟨d, d.lowerCharacter_eq_one_of_sourceQuotient_fixed p hp ξ ?_⟩
  have hsource : d.sourceQuotient = W :=
    W.normalizedData_sourceQuotient p hp ξ m hm
  rw [hsource]
  exact hfixed

/-- The complete selected stable-model certificate supplies the exact
generic curve, smooth connected fibre, pointed Jacobian, and split nodal
special fibre used by the cited Raynaud input. The resulting normalized
ordinary basis has trivial lower character at every RM label. -/
theorem exists_primePlusNormalizedOrdinaryDataLowerOne_of_stableModel
    (H : PrimePlusScaledStableModelData p hp ξ)
    (m : ℕ) (hm : m.Coprime (p ^ (0 + 1))) :
    ∃ d : PrimePlusNormalizedOrdinaryData p hp ξ m hm,
      d.lowerCharacter = 1 := by
  have hparameter : (H.T : realCyclotomicField p) =
      ξ.val / (2 - tau p 1) ^ p := H.field_parameter
  obtain ⟨D⟩ := exists_primePlusRaynaudUniformization_of_scaledModel p hp ξ
    H.T H.special_geometry hparameter (primePlusRealScaledFiberJacobian p hp ξ)
  exact D.existsNormalizedOrdinaryDataLowerOne p hp ξ m hm

/-- At the actual rational zero cusp, the normalized lower character on the
selected covariant RM Tate factor is exactly one. No complementary-fibre
comparison is used in this branch. -/
theorem exists_primePlusNormalizedOrdinaryDataLowerOne_at_cubicNumerator
    (ξ₀ : ProjectiveLine.Parameter ℚ) {A : ℤ} {B : ℕ}
    (hξ : ξ₀.val = (A : ℚ) / B) (hA : A ≠ 0) (hB : B ≠ 0)
    (hAB : Int.gcd A B = 1) (hdeep : (p : ℤ) ^ 3 ∣ A)
    (m : ℕ) (hm : m.Coprime (p ^ (0 + 1))) :
    ∃ d : PrimePlusNormalizedOrdinaryData p hp
        (darmonRationalParameter p ξ₀) m hm,
      d.lowerCharacter = 1 := by
  let H := PrimePlusScaledStableModelData.of_cubicNumerator p hp ξ₀
    hξ hA hB hAB hdeep
  exact exists_primePlusNormalizedOrdinaryDataLowerOne_of_stableModel p hp
    (darmonRationalParameter p ξ₀) H m hm

/-- The manuscript's local ordinary deduction, now fed by a period lattice
for its selected proper flat scaled model and the same pointed Jacobian. -/
theorem nonempty_primePlusOrdinaryQuotient_of_scaledModel
    (T : (realPrimeAboveConductor p).valuationSubringAtPrime
      (realCyclotomicField p))
    (hgeometry : CyclotomicStableGeometry p T)
    (hparameter : (T : realCyclotomicField p) =
      ξ.val / (2 - tau p 1) ^ p)
    (m : ℕ) (hm : m.Coprime (p ^ (0 + 1))) :
    Nonempty (PrimePlusOrdinaryQuotient p hp ξ m hm) := by
  let hJacobian := primePlusRealScaledFiberJacobian p hp ξ
  obtain ⟨D⟩ := exists_primePlusRaynaudUniformization_of_scaledModel p hp ξ
    T hgeometry hparameter hJacobian
  let : Module (RealPrimePowerCompletion p 0) D.Y := D.YRealModule
  let : IsScalarTower ℚ_[p] (RealPrimePowerCompletion p 0) D.Y :=
    D.YScalarTower
  let : Module.Finite ℚ_[p] D.Y := D.YFinite
  exact nonempty_primePlusOrdinaryQuotient_of_RaynaudSplitPairing p hp ξ
    D.Y D.periodMap D.periodMap_surjective D.Yrank D.YAction
    D.periodMap_equivariant D.X D.XAction D.splitTorus
    D.rationalPairing D.rationalPairing_nondegenerate
    D.rationalPairing_equivariant m hm

/-- An actual selected scaled parameter of positive local valuation supplies
the integral model in the semistable Picard interface. The local valuation
ring element and its zero residue are constructed from that parameter. -/
theorem nonempty_primePlusOrdinaryQuotient_of_scaledPositiveValuation
    (hval : (realPrimeAboveConductor p).valuation (realCyclotomicField p)
      (ξ.val / (2 - tau p 1) ^ p) < 1)
    (m : ℕ) (hm : m.Coprime (p ^ (0 + 1))) :
    Nonempty (PrimePlusOrdinaryQuotient p hp ξ m hm) := by
  let t : realCyclotomicField p := ξ.val / (2 - tau p 1) ^ p
  let P := realPrimeAboveConductor p
  have ht : t ≠ 0 := div_ne_zero ξ.property.1
    (pow_ne_zero _ (realCyclotomicScale_ne_zero p))
  let T := P.localElement t hval.le
  have hTne : T ≠ 0 := by
    intro h
    exact ht (congrArg (fun x : P.valuationSubringAtPrime
      (realCyclotomicField p) => (x : realCyclotomicField p)) h)
  have hres : P.specialization t hval.le = 0 := by
    by_contra h
    have hv := (P.specialization_ne_zero_iff t hval.le).mp h
    exact (not_le_of_gt hval) hv.ge
  have hTzero : realLocalReduction p T = 0 := by
    change realCyclotomicResidueEquiv p (P.specialization t hval.le) = 0
    rw [hres, map_zero]
  have hgeometry : CyclotomicStableGeometry.{0, 0, 0, 0, 0, 0} p T :=
    cyclotomicStableGeometry_of_five_le p hp T hTne hTzero
  exact nonempty_primePlusOrdinaryQuotient_of_scaledModel p hp ξ T
    hgeometry rfl m hm

/-- [TripathiGoswami, Proposition `prime-deep-DO`, first cusp] A rational
parameter with numerator divisible by `p³` gives the actual selected plus
Jacobian a rank-one, weight-zero ordinary quotient. The new admission used here is the named semistable Picard/Raynaud
interface above; the selected family and Hodge inputs remain conditional. -/
theorem nonempty_primePlusOrdinaryQuotient_at_cubic_numerator
    (ξ₀ : ProjectiveLine.Parameter ℚ) {A : ℤ} {B : ℕ}
    (hξ : ξ₀.val = (A : ℚ) / B) (hA : A ≠ 0) (hB : B ≠ 0)
    (hAB : Int.gcd A B = 1) (hdeep : (p : ℤ) ^ 3 ∣ A)
    (m : ℕ) (hm : m.Coprime (p ^ (0 + 1))) :
    Nonempty (PrimePlusOrdinaryQuotient p hp
      (darmonRationalParameter p ξ₀) m hm) := by
  apply nonempty_primePlusOrdinaryQuotient_of_scaledPositiveValuation p hp
    (darmonRationalParameter p ξ₀)
  exact (primePlusScaledParameter_lt_one_iff_cubic_numerator p hp ξ₀
    hξ hA hB hAB).2 hdeep

/-- The zero-cusp branch supplies a normalized local ordinary basis with no
complementary-cusp twist hypothesis. This is the basis to use when comparing
the selected native residual lattice in the Skinner–Wiles checklist. -/
theorem nonempty_primePlusNormalizedOrdinaryData_at_cubic_numerator
    (ξ₀ : ProjectiveLine.Parameter ℚ) {A : ℤ} {B : ℕ}
    (hξ : ξ₀.val = (A : ℚ) / B) (hA : A ≠ 0) (hB : B ≠ 0)
    (hAB : Int.gcd A B = 1) (hdeep : (p : ℤ) ^ 3 ∣ A)
    (m : ℕ) (hm : m.Coprime (p ^ (0 + 1))) :
    Nonempty (PrimePlusNormalizedOrdinaryData p hp
      (darmonRationalParameter p ξ₀) m hm) := by
  obtain ⟨W⟩ := nonempty_primePlusOrdinaryQuotient_at_cubic_numerator p hp ξ₀
    hξ hA hB hAB hdeep m hm
  exact W.exists_normalizedOrdinaryData p hp (darmonRationalParameter p ξ₀) m hm

/-- A single selected normalized ordinary basis at the zero cusp. Its source
is the cited Raynaud period construction on the same Jacobian; no ordinary
basis is separately assumed. -/
noncomputable def primePlusRaynaudCubicNumeratorOrdinaryData
    (ξ₀ : ProjectiveLine.Parameter ℚ) {A : ℤ} {B : ℕ}
    (hξ : ξ₀.val = (A : ℚ) / B) (hA : A ≠ 0) (hB : B ≠ 0)
    (hAB : Int.gcd A B = 1) (hdeep : (p : ℤ) ^ 3 ∣ A)
    (m : ℕ) (hm : m.Coprime (p ^ (0 + 1))) :
    PrimePlusNormalizedOrdinaryData p hp (darmonRationalParameter p ξ₀) m hm :=
  Classical.choose <| exists_primePlusNormalizedOrdinaryDataLowerOne_at_cubicNumerator
    p hp ξ₀ hξ hA hB hAB hdeep m hm

/-- The chosen lower character at the actual zero cusp is trivial. -/
theorem primePlusRaynaudCubicNumeratorOrdinaryData_lowerCharacter_eq_one
    (ξ₀ : ProjectiveLine.Parameter ℚ) {A : ℤ} {B : ℕ}
    (hξ : ξ₀.val = (A : ℚ) / B) (hA : A ≠ 0) (hB : B ≠ 0)
    (hAB : Int.gcd A B = 1) (hdeep : (p : ℤ) ^ 3 ∣ A)
    (m : ℕ) (hm : m.Coprime (p ^ (0 + 1))) :
    (primePlusRaynaudCubicNumeratorOrdinaryData p hp ξ₀
      hξ hA hB hAB hdeep m hm).lowerCharacter = 1 :=
  Classical.choose_spec <|
    exists_primePlusNormalizedOrdinaryDataLowerOne_at_cubicNumerator
      p hp ξ₀ hξ hA hB hAB hdeep m hm

/-- The complementary rational cusp has the same ordinary quotient for the
selected plus Jacobian at `1 - ξ`. Transport to the fibre at `ξ` is a separate
chosen-family involution comparison. -/
theorem nonempty_primePlusOrdinaryQuotient_at_cubic_difference
    (ξ₀ : ProjectiveLine.Parameter ℚ) {A : ℤ} {B : ℕ}
    (hξ : ξ₀.val = (A : ℚ) / B) (hB : B ≠ 0)
    (hAB : Int.gcd A B = 1) (hdeep : (p : ℤ) ^ 3 ∣ ((B : ℤ) - A))
    (m : ℕ) (hm : m.Coprime (p ^ (0 + 1))) :
    Nonempty (PrimePlusOrdinaryQuotient p hp
      (darmonRationalParameter p (ProjectiveLine.complementParameter ℚ ξ₀))
      m hm) := by
  apply nonempty_primePlusOrdinaryQuotient_of_scaledPositiveValuation p hp
    (darmonRationalParameter p (ProjectiveLine.complementParameter ℚ ξ₀))
  exact (primePlusComplementScaledParameter_lt_one_iff_cubic_difference
    p hp ξ₀ hξ hB hAB).2 hdeep

/-- The two deep-cusp alternatives give `DO` on the original selected plus
Jacobian. At the complementary cusp the precise finite-order twisted Tate
intertwiner remains explicit; the Raynaud period comparison is now constructed
from the actual scaled model in both cases. -/
theorem nonempty_primePlusOrdinaryQuotient_at_deep_cusp
    (ξ₀ : ProjectiveLine.Parameter ℚ) {A : ℤ} {B : ℕ}
    (hξ : ξ₀.val = (A : ℚ) / B) (hA : A ≠ 0) (hB : B ≠ 0)
    (hAB : Int.gcd A B = 1)
    (χ : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0) →*
      (RealPrimePowerCompletion p 0)ˣ) (hχ : Continuous χ)
    (horder : IsOfFinOrder χ)
    (e : (((Representation.ofCharacter χ).tprod
      (primePlusDecompositionRepresentation p hp
        (ProjectiveLine.complementParameter (realCyclotomicField p)
          (darmonRationalParameter p ξ₀))).ρ).Equiv
      (primePlusDecompositionRepresentation p hp
        (darmonRationalParameter p ξ₀)).ρ))
    (hdeep : (p : ℤ) ^ 3 ∣ A ∨ (p : ℤ) ^ 3 ∣ ((B : ℤ) - A))
    (m : ℕ) (hm : m.Coprime (p ^ (0 + 1))) :
    Nonempty (PrimePlusOrdinaryQuotient p hp
      (darmonRationalParameter p ξ₀) m hm) := by
  rcases hdeep with hzero | hone
  · exact nonempty_primePlusOrdinaryQuotient_at_cubic_numerator p hp ξ₀
      hξ hA hB hAB hzero m hm
  · have hbase : Nonempty (PrimePlusOrdinaryQuotient p hp
        (ProjectiveLine.complementParameter (realCyclotomicField p)
          (darmonRationalParameter p ξ₀)) 1 (Nat.coprime_one_left _)) := by
      rw [← darmonRationalParameter_complement p ξ₀]
      exact nonempty_primePlusOrdinaryQuotient_at_cubic_difference p hp ξ₀
        hξ hB hAB hone 1 (Nat.coprime_one_left _)
    exact nonempty_primePlusOrdinaryQuotient_of_complement_twist p hp
      (darmonRationalParameter p ξ₀) χ hχ horder e m hm hbase

/-- The deep-cusp ordinary quotient supplies the selected weight-zero basis
needed by the local Skinner–Wiles comparison. Its existential source is the
named Picard/Raynaud interface and, for the second cusp, the displayed Tate
intertwiner. -/
theorem nonempty_primePlusNormalizedOrdinaryData_at_deep_cusp
    (ξ₀ : ProjectiveLine.Parameter ℚ) {A : ℤ} {B : ℕ}
    (hξ : ξ₀.val = (A : ℚ) / B) (hA : A ≠ 0) (hB : B ≠ 0)
    (hAB : Int.gcd A B = 1)
    (χ : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0) →*
      (RealPrimePowerCompletion p 0)ˣ) (hχ : Continuous χ)
    (horder : IsOfFinOrder χ)
    (e : (((Representation.ofCharacter χ).tprod
      (primePlusDecompositionRepresentation p hp
        (ProjectiveLine.complementParameter (realCyclotomicField p)
          (darmonRationalParameter p ξ₀))).ρ).Equiv
      (primePlusDecompositionRepresentation p hp
        (darmonRationalParameter p ξ₀)).ρ))
    (hdeep : (p : ℤ) ^ 3 ∣ A ∨ (p : ℤ) ^ 3 ∣ ((B : ℤ) - A))
    (m : ℕ) (hm : m.Coprime (p ^ (0 + 1))) :
    Nonempty (PrimePlusNormalizedOrdinaryData p hp
      (darmonRationalParameter p ξ₀) m hm) := by
  obtain ⟨W⟩ := nonempty_primePlusOrdinaryQuotient_at_deep_cusp p hp ξ₀
    hξ hA hB hAB χ hχ horder e hdeep m hm
  exact W.exists_normalizedOrdinaryData p hp (darmonRationalParameter p ξ₀) m hm

end HilbertModularity.Hypergeometric
