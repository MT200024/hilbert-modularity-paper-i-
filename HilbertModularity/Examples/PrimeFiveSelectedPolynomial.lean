/- Assembled by AxiomProver. -/

module
public import HilbertModularity.Examples.PrimeFiveModelFrobeniusCarriers
public import HilbertModularity.Examples.PrimeFiveSelectedSpecialFiber
public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Tactic.FastInstance
/-! # The selected level-five special Jacobian polynomial

The pointed Jacobian count is carried through an abstract dual Tate space
before inserting the selected residue quotient. Its numerical polynomial is
proved from the checked projective counts and the cited general cohomology
comparison, with no numerical or RM-label admission.
-/

public noncomputable section
open CategoryTheory AlgebraicGeometry IsDedekindDomain
open scoped NumberField
namespace HilbertModularity.Examples
open _root_.HilbertModularity.Cyclotomic Hyperelliptic GroupScheme
attribute [local instance] Ideal.Quotient.field
@[instance_reducible] local instance carrierQuotientCommRing
    (P : HeightOneSpectrum (𝓞 (realCyclotomicField 5))) :
    CommRing (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal) :=
  (Ideal.Quotient.field P.asIdeal).toCommRing
local instance wrapperFiveFact : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance wrapperElevenFact : Fact (Nat.Prime 11) := ⟨by decide⟩
/-- A named carrier for the same cohomological dual Tate space. The linear
equivalence below retains the original scalar action and Frobenius map. -/
structure DualTateCarrier (k : Type*) [Field k]
    (J : CommGrp (Over (Spec (CommRingCat.of k))))
    (p : ℕ) [Fact p.Prime] where
  val : Module.Dual ℚ_[p] (GroupScheme.rationalTate k J.X p)
def DualTateCarrier.toUnderlying (k : Type*) [Field k]
    (J : CommGrp (Over (Spec (CommRingCat.of k))))
    (p : ℕ) [Fact p.Prime] :
    DualTateCarrier k J p ≃ Module.Dual ℚ_[p] (GroupScheme.rationalTate k J.X p) where
  toFun := DualTateCarrier.val
  invFun := DualTateCarrier.mk
  left_inv := by intro x; cases x; rfl
  right_inv := by intro x; rfl
instance DualTateCarrier.addCommGroup (k : Type*) [Field k]
    (J : CommGrp (Over (Spec (CommRingCat.of k))))
    (p : ℕ) [Fact p.Prime] : AddCommGroup (DualTateCarrier k J p) :=
  Equiv.addCommGroup (DualTateCarrier.toUnderlying k J p)
def DualTateCarrier.toUnderlyingAdd (k : Type*) [Field k]
    (J : CommGrp (Over (Spec (CommRingCat.of k))))
    (p : ℕ) [Fact p.Prime] :
    DualTateCarrier k J p ≃+ Module.Dual ℚ_[p] (GroupScheme.rationalTate k J.X p) :=
  { DualTateCarrier.toUnderlying k J p with map_add' := by intro x y; rfl }
@[instance_reducible] instance DualTateCarrier.module (k : Type*) [Field k]
    (J : CommGrp (Over (Spec (CommRingCat.of k))))
    (p : ℕ) [Fact p.Prime] : Module ℚ_[p] (DualTateCarrier k J p) :=
  fast_instance% AddEquiv.module ℚ_[p] (DualTateCarrier.toUnderlyingAdd k J p)
def DualTateCarrier.toUnderlyingLinear (k : Type*) [Field k]
    (J : CommGrp (Over (Spec (CommRingCat.of k))))
    (p : ℕ) [Fact p.Prime] :
    DualTateCarrier k J p ≃ₗ[ℚ_[p]] Module.Dual ℚ_[p] (GroupScheme.rationalTate k J.X p) :=
  { DualTateCarrier.toUnderlyingAdd k J p with map_smul' := by intro a x; rfl }
def DualTateCarrier.geometricFrobenius (k : Type*) [Field k] [Fintype k]
    (J : CommGrp (Over (Spec (CommRingCat.of k))))
    (p : ℕ) [Fact p.Prime] : Module.End ℚ_[p] (DualTateCarrier k J p) :=
  (DualTateCarrier.toUnderlyingLinear k J p).symm.conj
    ((GroupScheme.tateRepresentation k J.X p).dual
      (Hyperelliptic.finiteFieldGeometricFrobenius k))

/-- The named carrier uses exactly the original cohomological Frobenius,
conjugated by its scalar-preserving linear equivalence. -/
theorem DualTateCarrier.geometricFrobenius_eq_conj
    (k : Type*) [Field k] [Fintype k]
    (J : CommGrp (Over (Spec (CommRingCat.of k))))
    (p : ℕ) [Fact p.Prime] :
    DualTateCarrier.geometricFrobenius k J p =
      (DualTateCarrier.toUnderlyingLinear k J p).symm.conj
        ((GroupScheme.tateRepresentation k J.X p).dual
          (Hyperelliptic.finiteFieldGeometricFrobenius k)) := (rfl)

theorem DualTateCarrier.toUnderlying_conj_geometricFrobenius
    (k : Type*) [Field k] [Fintype k]
    (J : CommGrp (Over (Spec (CommRingCat.of k))))
    (p : ℕ) [Fact p.Prime] :
    (DualTateCarrier.toUnderlyingLinear k J p).conj
      (DualTateCarrier.geometricFrobenius k J p) =
        (GroupScheme.tateRepresentation k J.X p).dual
          (Hyperelliptic.finiteFieldGeometricFrobenius k) := by
  rw [DualTateCarrier.geometricFrobenius_eq_conj]
  ext v
  simp [LinearEquiv.conj_apply]

/-- A pointed Jacobian over an abstract field, prior to inserting the
selected number-field residue quotient. -/
structure PrimeFivePointedData (k : Type*) [Field k] where
  jacobian : CommGrp (Over (Spec (CommRingCat.of k)))
  point : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
    Over.mk (AlgebraicGeometry.Hyperelliptic.toSpec
      (primeFivePolynomial k) 3 (primeFivePolynomial_degree k))
  pointed : PointedCurveJacobian k
    (Over.mk (AlgebraicGeometry.Hyperelliptic.toSpec
      (primeFivePolynomial k) 3 (primeFivePolynomial_degree k)))
    point jacobian

theorem toMatrix_conj_under_basis
    {R V W ι : Type*} [Field R]
    [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W]
    [Fintype ι] [DecidableEq ι]
    (e : V ≃ₗ[R] W) (b : Module.Basis ι R V) (f : Module.End R V) :
    LinearMap.toMatrix (b.map e) (b.map e) (e.conj f) =
      LinearMap.toMatrix b b f := by
  rw [LinearMap.toMatrix_map_left, LinearMap.toMatrix_map_right]
  congr 1
  ext v
  change e.symm (e.conj f (e v)) = f v
  simp [LinearEquiv.conj_apply]

/-- The eleven-prime numerical polynomial on the pointed Jacobian's dual
Tate action, expressed on the equivalent named carrier. -/
def PointedPolynomial11
    (k : Type*) [Field k] [Fintype k] (D : PrimeFivePointedData k) : Prop :=
    ∃ b : Module.Basis (Fin 4) ℚ_[5] (DualTateCarrier k D.jacobian 5),
      (LinearMap.toMatrix b b
        (DualTateCarrier.geometricFrobenius k D.jacobian 5)).charpolyRev =
        primeFiveNumericalPolynomial11 ℚ_[5]

/-- The same polynomial on the actual dual rational Tate representation. -/
def RawSpecialPolynomial11
    (k : Type*) [Field k] [Fintype k]
    (J : CommGrp (Over (Spec (CommRingCat.of k)))) : Prop :=
    ∃ b : Module.Basis (Fin 4) ℚ_[5]
      (Module.Dual ℚ_[5] (GroupScheme.rationalTate k J.X 5)),
      (LinearMap.toMatrix b b
        ((GroupScheme.tateRepresentation k J.X 5).dual
          (Hyperelliptic.finiteFieldGeometricFrobenius k))).charpolyRev =
        primeFiveNumericalPolynomial11 ℚ_[5]

/-- Extract the basis and polynomial identity from the raw special-fibre
certificate without unfolding its definition downstream. -/
theorem RawSpecialPolynomial11.exists_basis
    (k : Type*) [Field k] [Fintype k]
    (J : CommGrp (Over (Spec (CommRingCat.of k))))
    (h : RawSpecialPolynomial11 k J) :
    ∃ b : Module.Basis (Fin 4) ℚ_[5]
      (Module.Dual ℚ_[5] (GroupScheme.rationalTate k J.X 5)),
      (LinearMap.toMatrix b b
        ((GroupScheme.tateRepresentation k J.X 5).dual
          (Hyperelliptic.finiteFieldGeometricFrobenius k))).charpolyRev =
        primeFiveNumericalPolynomial11 ℚ_[5] := by
  exact h

theorem PointedPolynomial11.toRaw
    (k : Type*) [Field k] [Fintype k]
    (D : PrimeFivePointedData k) (h : PointedPolynomial11 k D) :
    RawSpecialPolynomial11 k D.jacobian := by
  change ∃ b : Module.Basis (Fin 4) ℚ_[5] (DualTateCarrier k D.jacobian 5),
    (LinearMap.toMatrix b b
      (DualTateCarrier.geometricFrobenius k D.jacobian 5)).charpolyRev =
      primeFiveNumericalPolynomial11 ℚ_[5] at h
  change ∃ b : Module.Basis (Fin 4) ℚ_[5]
    (Module.Dual ℚ_[5] (GroupScheme.rationalTate k D.jacobian.X 5)),
    (LinearMap.toMatrix b b
      ((GroupScheme.tateRepresentation k D.jacobian.X 5).dual
        (Hyperelliptic.finiteFieldGeometricFrobenius k))).charpolyRev =
      primeFiveNumericalPolynomial11 ℚ_[5]
  obtain ⟨b, hb⟩ := h
  let e := DualTateCarrier.toUnderlyingLinear k D.jacobian 5
  refine ⟨b.map e, ?_⟩
  have he : e.conj (DualTateCarrier.geometricFrobenius k D.jacobian 5) =
      (GroupScheme.tateRepresentation k D.jacobian.X 5).dual
        (Hyperelliptic.finiteFieldGeometricFrobenius k) := by
    ext v
    simp [e, DualTateCarrier.geometricFrobenius, LinearEquiv.conj_apply]
  rw [← he, toMatrix_conj_under_basis]
  exact hb

/-- The checked genus-two point counts imply the full dual Tate polynomial.
The general Abel–Jacobi/cohomology comparison is the cited literature input
in [MilneJacobian2021] and [MilneAV]. -/
theorem countedPolynomial11OfData
    (k : Type*) [Field k] [Fintype k] (hk : Fintype.card k = 11)
    (D : PrimeFivePointedData k) : PointedPolynomial11 k D := by
  change ∃ b : Module.Basis (Fin 4) ℚ_[5] (DualTateCarrier k D.jacobian 5),
    (LinearMap.toMatrix b b
      (DualTateCarrier.geometricFrobenius k D.jacobian 5)).charpolyRev =
      primeFiveNumericalPolynomial11 ℚ_[5]
  let e : k ≃+* ZMod 11 :=
    FiniteField.ringEquivOfCardEq (by simpa [ZMod.card] using hk)
  let : Algebra k QuadraticField11 :=
    ((algebraMap (ZMod 11) QuadraticField11).comp e.toRingHom).toAlgebra
  have h2k : (2 : k) ≠ 0 := by
    intro h
    have he : (2 : ZMod 11) = 0 := by
      calc
        (2 : ZMod 11) = e (2 : k) := (map_ofNat e 2).symm
        _ = e 0 := congrArg e h
        _ = 0 := map_zero e
    exact (by decide : (2 : ZMod 11) ≠ 0) he
  have hsep : (primeFivePolynomial k).Separable :=
    primeFivePolynomial_separable_of_card_eq_11 hk
  let b := primeFive_pointedJacobianBasis11_at_five
    k QuadraticField11 hk quadraticField11_card hsep h2k
    D.jacobian D.point D.pointed
  have hb := primeFive_pointedJacobianBasis11_at_five_charpolyRev
    k QuadraticField11 hk quadraticField11_card hsep h2k
    D.jacobian D.point D.pointed
  let d := (DualTateCarrier.toUnderlyingLinear k D.jacobian 5).symm
  refine ⟨b.map d, ?_⟩
  change (LinearMap.toMatrix (b.map d) (b.map d)
    (d.conj ((tateRepresentation k D.jacobian.X 5).dual
      (Hyperelliptic.finiteFieldGeometricFrobenius k)))).charpolyRev = _
  rw [toMatrix_conj_under_basis]
  exact hb

theorem selectedWrappedPolynomial11OfData
    (P : HeightOneSpectrum (𝓞 (realCyclotomicField 5)))
    [Fintype (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal)]
    (hk : Fintype.card (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal) = 11)
    (D : PrimeFivePointedData (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal)) :
    PointedPolynomial11 (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal) D := by
  apply countedPolynomial11OfData
  exact hk

/-- The pointed Jacobian is the actual special fibre of `W.model`. -/
def selectedPointedData
    (P : HeightOneSpectrum (𝓞 (realCyclotomicField 5)))
    (W : PrimeFiveSelectedSpecialJacobian P) :
    PrimeFivePointedData (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal) :=
  { jacobian := localSpecialFiber (realCyclotomicField 5) P W.model
    point := W.specialPoint
    pointed := W.specialJacobian }

theorem selectedPointedData_jacobian
    (P : HeightOneSpectrum (𝓞 (realCyclotomicField 5)))
    (W : PrimeFiveSelectedSpecialJacobian P) :
    (selectedPointedData P W).jacobian =
      localSpecialFiber (realCyclotomicField 5) P W.model := (rfl)

theorem selectedWrappedPolynomial11
    (P : HeightOneSpectrum (𝓞 (realCyclotomicField 5)))
    (W : PrimeFiveSelectedSpecialJacobian P)
    [Fintype (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal)]
    (hk : Fintype.card (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal) = 11) :
    PointedPolynomial11 (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal)
      (selectedPointedData P W) := by
  apply selectedWrappedPolynomial11OfData
  exact hk

/-- The selected model's actual special Jacobian has the numerical
eleven-prime full cohomological Frobenius polynomial. -/
theorem selectedRawSpecialPolynomial11
    (P : HeightOneSpectrum (𝓞 (realCyclotomicField 5)))
    (W : PrimeFiveSelectedSpecialJacobian P)
    [Fintype (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal)]
    (hk : Fintype.card (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal) = 11) :
    RawSpecialPolynomial11 (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal)
      (selectedPointedData P W).jacobian := by
  apply PointedPolynomial11.toRaw
  exact selectedWrappedPolynomial11 P W hk


end HilbertModularity.Examples
