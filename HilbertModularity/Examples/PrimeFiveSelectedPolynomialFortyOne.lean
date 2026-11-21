/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Examples.PrimeFiveSelectedPolynomial

/-! # The forty-one-prime polynomial on the selected Jacobian

The same selected-model and abstract-carrier construction applies to the
second degree-one prime, using its checked point counts over fields of sizes
41 and 1681.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry IsDedekindDomain
open scoped NumberField

namespace HilbertModularity.Examples

open _root_.HilbertModularity.Cyclotomic Hyperelliptic GroupScheme

attribute [local instance] Ideal.Quotient.field
@[instance_reducible] local instance selectedFortyOneQuotientCommRing
    (P : HeightOneSpectrum (𝓞 (realCyclotomicField 5))) :
    CommRing (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal) :=
  (Ideal.Quotient.field P.asIdeal).toCommRing
local instance selectedFortyOneFiveFact : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance selectedFortyOneFact : Fact (Nat.Prime 41) := ⟨by decide⟩

/-- The forty-one-prime numerical polynomial on the equivalent named dual
Tate carrier of a pointed Jacobian. -/
def PointedPolynomial41
    (k : Type*) [Field k] [Fintype k] (D : PrimeFivePointedData k) : Prop :=
    ∃ b : Module.Basis (Fin 4) ℚ_[5] (DualTateCarrier k D.jacobian 5),
      (LinearMap.toMatrix b b
        (DualTateCarrier.geometricFrobenius k D.jacobian 5)).charpolyRev =
        primeFiveNumericalPolynomial41 ℚ_[5]

/-- The same polynomial on the original cohomological dual Tate space. -/
def RawSpecialPolynomial41
    (k : Type*) [Field k] [Fintype k]
    (J : CommGrp (Over (Spec (CommRingCat.of k)))) : Prop :=
    ∃ b : Module.Basis (Fin 4) ℚ_[5]
      (Module.Dual ℚ_[5] (GroupScheme.rationalTate k J.X 5)),
      (LinearMap.toMatrix b b
        ((GroupScheme.tateRepresentation k J.X 5).dual
          (Hyperelliptic.finiteFieldGeometricFrobenius k))).charpolyRev =
        primeFiveNumericalPolynomial41 ℚ_[5]

theorem RawSpecialPolynomial41.exists_basis
    (k : Type*) [Field k] [Fintype k]
    (J : CommGrp (Over (Spec (CommRingCat.of k))))
    (h : RawSpecialPolynomial41 k J) :
    ∃ b : Module.Basis (Fin 4) ℚ_[5]
      (Module.Dual ℚ_[5] (GroupScheme.rationalTate k J.X 5)),
      (LinearMap.toMatrix b b
        ((GroupScheme.tateRepresentation k J.X 5).dual
          (Hyperelliptic.finiteFieldGeometricFrobenius k))).charpolyRev =
        primeFiveNumericalPolynomial41 ℚ_[5] := by
  exact h

theorem PointedPolynomial41.toRaw
    (k : Type*) [Field k] [Fintype k]
    (D : PrimeFivePointedData k) (h : PointedPolynomial41 k D) :
    RawSpecialPolynomial41 k D.jacobian := by
  change ∃ b : Module.Basis (Fin 4) ℚ_[5] (DualTateCarrier k D.jacobian 5),
    (LinearMap.toMatrix b b
      (DualTateCarrier.geometricFrobenius k D.jacobian 5)).charpolyRev =
      primeFiveNumericalPolynomial41 ℚ_[5] at h
  change ∃ b : Module.Basis (Fin 4) ℚ_[5]
    (Module.Dual ℚ_[5] (GroupScheme.rationalTate k D.jacobian.X 5)),
    (LinearMap.toMatrix b b
      ((GroupScheme.tateRepresentation k D.jacobian.X 5).dual
        (Hyperelliptic.finiteFieldGeometricFrobenius k))).charpolyRev =
      primeFiveNumericalPolynomial41 ℚ_[5]
  obtain ⟨b, hb⟩ := h
  let e := DualTateCarrier.toUnderlyingLinear k D.jacobian 5
  refine ⟨b.map e, ?_⟩
  have he : e.conj (DualTateCarrier.geometricFrobenius k D.jacobian 5) =
      (GroupScheme.tateRepresentation k D.jacobian.X 5).dual
        (Hyperelliptic.finiteFieldGeometricFrobenius k) := by
    exact DualTateCarrier.toUnderlying_conj_geometricFrobenius k D.jacobian 5
  rw [← he, toMatrix_conj_under_basis]
  exact hb

/-- The checked two point counts imply the full cohomological polynomial for
every pointed Jacobian of the displayed reduced curve over a field of size
41. The general cohomology input is [MilneJacobian2021] and [MilneAV]. -/
theorem countedPolynomial41OfData
    (k : Type*) [Field k] [Fintype k] (hk : Fintype.card k = 41)
    (D : PrimeFivePointedData k) : PointedPolynomial41 k D := by
  change ∃ b : Module.Basis (Fin 4) ℚ_[5] (DualTateCarrier k D.jacobian 5),
    (LinearMap.toMatrix b b
      (DualTateCarrier.geometricFrobenius k D.jacobian 5)).charpolyRev =
      primeFiveNumericalPolynomial41 ℚ_[5]
  let e : k ≃+* ZMod 41 :=
    FiniteField.ringEquivOfCardEq (by simpa [ZMod.card] using hk)
  let : Algebra k QuadraticField41 :=
    ((algebraMap (ZMod 41) QuadraticField41).comp e.toRingHom).toAlgebra
  have h2k : (2 : k) ≠ 0 := by
    intro h
    have he : (2 : ZMod 41) = 0 := by
      calc
        (2 : ZMod 41) = e (2 : k) := (map_ofNat e 2).symm
        _ = e 0 := congrArg e h
        _ = 0 := map_zero e
    exact (by decide : (2 : ZMod 41) ≠ 0) he
  have hsep : (primeFivePolynomial k).Separable :=
    primeFivePolynomial_separable_of_card_eq_41 hk
  let b := primeFive_pointedJacobianBasis41_at_five
    k QuadraticField41 hk quadraticField41_card hsep h2k
    D.jacobian D.point D.pointed
  have hb := primeFive_pointedJacobianBasis41_at_five_charpolyRev
    k QuadraticField41 hk quadraticField41_card hsep h2k
    D.jacobian D.point D.pointed
  let d := (DualTateCarrier.toUnderlyingLinear k D.jacobian 5).symm
  refine ⟨b.map d, ?_⟩
  rw [DualTateCarrier.geometricFrobenius_eq_conj]
  rw [toMatrix_conj_under_basis]
  exact hb

/-- The actual selected model's special Jacobian has the numerical
forty-one-prime full cohomological Frobenius polynomial. -/
theorem selectedRawSpecialPolynomial41
    (P : HeightOneSpectrum (𝓞 (realCyclotomicField 5)))
    (W : PrimeFiveSelectedSpecialJacobian P)
    [Fintype (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal)]
    (hk : Fintype.card (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal) = 41) :
    RawSpecialPolynomial41 (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal)
      (selectedPointedData P W).jacobian := by
  apply PointedPolynomial41.toRaw
  apply countedPolynomial41OfData
  exact hk

end HilbertModularity.Examples
