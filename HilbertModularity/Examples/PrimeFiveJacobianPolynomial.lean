/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Examples.PrimeFiveCohomologicalPolynomial
public import HilbertModularity.Geometry.Etale.FiniteFieldJacobianCohomology
import Mathlib.Tactic.NormNum

/-! # The reduced level-five curve and its actual pointed Jacobian

The checked finite-field point counts hold in every field of the stated
cardinality. The cited Abel–Jacobi and Tate comparison then transfers their
cohomological polynomial to the dual Tate action of the same Jacobian.
-/

public noncomputable section

open CategoryTheory Polynomial AlgebraicGeometry
open AlgebraicGeometry.GroupScheme

namespace HilbertModularity.Examples

open Hyperelliptic

local instance primeFiveJacobianPrime7 : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance primeFiveJacobianPrime5 : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance primeFiveJacobianPrime11 : Fact (Nat.Prime 11) := ⟨by decide⟩
local instance primeFiveJacobianPrime41 : Fact (Nat.Prime 41) := ⟨by decide⟩

/-- The displayed eleven-prime genus-two polynomial over a coefficient ring. -/
def primeFiveNumericalPolynomial11 (R : Type*) [CommRing R] : R[X] :=
  1 + X + 21 * X ^ 2 + 11 * X ^ 3 + 121 * X ^ 4

/-- The displayed forty-one-prime genus-two polynomial over a coefficient ring. -/
def primeFiveNumericalPolynomial41 (R : Type*) [CommRing R] : R[X] :=
  1 + X + 51 * X ^ 2 + 41 * X ^ 3 + 1681 * X ^ 4

/-- Literal coefficients of the counted eleven-prime polynomial. -/
theorem primeFiveNumericalPolynomial11_formula (R : Type*) [CommRing R] :
    primeFiveNumericalPolynomial11 R =
      1 + X + 21 * X ^ 2 + 11 * X ^ 3 + 121 * X ^ 4 := (rfl)

/-- Literal coefficients of the counted forty-one-prime polynomial. -/
theorem primeFiveNumericalPolynomial41_formula (R : Type*) [CommRing R] :
    primeFiveNumericalPolynomial41 R =
      1 + X + 51 * X ^ 2 + 41 * X ^ 3 + 1681 * X ^ 4 := (rfl)

/-- The literal eleven-prime polynomial is preserved by a change of
coefficient ring. -/
theorem primeFiveNumericalPolynomial11_map
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    (primeFiveNumericalPolynomial11 R).map f = primeFiveNumericalPolynomial11 S := by
  simp [primeFiveNumericalPolynomial11]

/-- The literal forty-one-prime polynomial is preserved by a change of
coefficient ring. -/
theorem primeFiveNumericalPolynomial41_map
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    (primeFiveNumericalPolynomial41 R).map f = primeFiveNumericalPolynomial41 S := by
  simp [primeFiveNumericalPolynomial41]

/-- The thirteen projective points are independent of the eleven-element
finite-field model. -/
theorem primeFive_count_of_card_eq_11 {k : Type*} [Field k] [Fintype k]
    [DecidableEq k] (hk : Fintype.card k = 11) :
    Nat.card (Scheme.RationalPoint (plusCurveToSpec 5 (by decide) (125 : k))) = 13 := by
  let e : ZMod 11 ≃+* k :=
    FiniteField.ringEquivOfCardEq (by simpa [ZMod.card] using hk.symm)
  let : CharP k 11 := charP_of_injective_ringHom (f := e.toRingHom) e.injective 11
  rw [primeFive_projective_card_euler (by rw [ringChar.eq k 11]; decide),
    ← primeFiveEulerCount_congr e]
  have h := primeFive_projective_card_euler (K := ZMod 11)
    (by rw [ringChar.eq (ZMod 11) 11]; decide)
  rw [primeFive_count_11] at h
  omega

/-- The forty-three projective points are independent of the
forty-one-element finite-field model. -/
theorem primeFive_count_of_card_eq_41 {k : Type*} [Field k] [Fintype k]
    [DecidableEq k] (hk : Fintype.card k = 41) :
    Nat.card (Scheme.RationalPoint (plusCurveToSpec 5 (by decide) (125 : k))) = 43 := by
  let e : ZMod 41 ≃+* k :=
    FiniteField.ringEquivOfCardEq (by simpa [ZMod.card] using hk.symm)
  let : CharP k 41 := charP_of_injective_ringHom (f := e.toRingHom) e.injective 41
  rw [primeFive_projective_card_euler (by rw [ringChar.eq k 41]; decide),
    ← primeFiveEulerCount_congr e]
  have h := primeFive_projective_card_euler (K := ZMod 41)
    (by rw [ringChar.eq (ZMod 41) 41]; decide)
  rw [primeFive_count_41] at h
  omega

private theorem natCast_ne_zero_of_not_dvd {k : Type*} [Field k]
    (p : ℕ) [CharP k p] (n : ℕ) (h : ¬ p ∣ n) : (n : k) ≠ 0 := by
  intro hn
  exact h ((CharP.cast_eq_zero_iff k p n).mp hn)

/-- Degree-six branch separability is automatic over every eleven-element
field, for the actual parameter 125. -/
theorem primeFivePolynomial_separable_of_card_eq_11 {k : Type*}
    [Field k] [Fintype k] (hk : Fintype.card k = 11) :
    (primeFivePolynomial k).Separable := by
  let e : ZMod 11 ≃+* k :=
    FiniteField.ringEquivOfCardEq (by simpa [ZMod.card] using hk.symm)
  let : CharP k 11 := charP_of_injective_ringHom (f := e.toRingHom) e.injective 11
  apply primeFivePolynomial_separable k
    (natCast_ne_zero_of_not_dvd 11 2 (by decide))
    (natCast_ne_zero_of_not_dvd 11 5 (by decide))
    (natCast_ne_zero_of_not_dvd 11 125 (by decide))
  intro h
  have h124 : (124 : k) ≠ 0 := natCast_ne_zero_of_not_dvd 11 124 (by decide)
  apply h124
  calc
    (124 : k) = 125 - 1 := by norm_num
    _ = 0 := sub_eq_zero.mpr h

/-- The same actual branch equation is separable over every
forty-one-element field. -/
theorem primeFivePolynomial_separable_of_card_eq_41 {k : Type*}
    [Field k] [Fintype k] (hk : Fintype.card k = 41) :
    (primeFivePolynomial k).Separable := by
  let e : ZMod 41 ≃+* k :=
    FiniteField.ringEquivOfCardEq (by simpa [ZMod.card] using hk.symm)
  let : CharP k 41 := charP_of_injective_ringHom (f := e.toRingHom) e.injective 41
  apply primeFivePolynomial_separable k
    (natCast_ne_zero_of_not_dvd 41 2 (by decide))
    (natCast_ne_zero_of_not_dvd 41 5 (by decide))
    (natCast_ne_zero_of_not_dvd 41 125 (by decide))
  intro h
  have h124 : (124 : k) ≠ 0 := natCast_ne_zero_of_not_dvd 41 124 (by decide)
  apply h124
  calc
    (124 : k) = 125 - 1 := by norm_num
    _ = 0 := sub_eq_zero.mpr h

/-- The actual pointed Jacobian of the reduced level-five curve has the
eleven-prime polynomial under geometric Frobenius on its cohomological dual
Tate action. The curve count and polynomial are proved, while the general
Abel–Jacobi cohomology comparison remains a visible literature premise. -/
theorem primeFive_pointedJacobian_geometricFrobeniusPolynomial_11
    (k k₂ : Type*) [Field k] [Fintype k] [Field k₂] [Fintype k₂]
    [Algebra k k₂] (hk : Fintype.card k = 11) (hk₂ : Fintype.card k₂ = 121)
    (hsep : (primeFivePolynomial k).Separable) (h2 : (2 : k) ≠ 0)
    (J : CommGrp (Over (Spec (CommRingCat.of k))))
    (b₀ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
      Over.mk (AlgebraicGeometry.Hyperelliptic.toSpec (primeFivePolynomial k) 3
        (primeFivePolynomial_degree k)))
    (hJ : PointedCurveJacobian k
      (Over.mk (AlgebraicGeometry.Hyperelliptic.toSpec (primeFivePolynomial k) 3
        (primeFivePolynomial_degree k))) b₀ J) :
    ∃ b : Module.Basis (Fin 4) ℚ_[7] (Module.Dual ℚ_[7] (rationalTate k J.X 7)),
      (LinearMap.toMatrix b b
        ((tateRepresentation k J.X 7).dual
          (AlgebraicGeometry.Hyperelliptic.finiteFieldGeometricFrobenius k))).charpolyRev =
        1 + X + 21 * X ^ 2 + 11 * X ^ 3 + 121 * X ^ 4 := by
  classical
  let f := primeFivePolynomial k
  have hd : f.natDegree = 2 * 3 := primeFivePolynomial_degree k
  have hd₂ : (f.map (algebraMap k k₂)).natDegree = 2 * 3 := by
    simpa only [f, primeFivePolynomial_map] using primeFivePolynomial_degree k₂
  have h₁ : Nat.card (Scheme.RationalPoint
      (AlgebraicGeometry.Hyperelliptic.toSpec f 3 hd)) = 13 := by
    exact (rationalPointCount_congr (plusPolynomial_five k).symm (by decide) hd
      (plusPolynomial_evenDegree 5 (by decide) (125 : k))).trans
        (primeFive_count_of_card_eq_11 hk)
  have h₂ : Nat.card (Scheme.RationalPoint
      (AlgebraicGeometry.Hyperelliptic.toSpec
        (f.map (algebraMap k k₂)) 3 hd₂)) = 163 := by
    have heq : f.map (algebraMap k k₂) = plusPolynomial 5 (125 : k₂) := by
      simpa only [f, primeFivePolynomial_map] using (plusPolynomial_five k₂).symm
    exact (rationalPointCount_congr heq (by decide) hd₂
      (plusPolynomial_evenDegree 5 (by decide) (125 : k₂))).trans
        (primeFive_count_of_card_eq_121 hk₂)
  obtain ⟨b, hb⟩ := AlgebraicGeometry.Hyperelliptic.genusTwoPointedJacobian_geometricFrobeniusPolynomial
    k f hd (primeFivePolynomial_monic k) hsep h2 7 (by
      let e : ZMod 11 ≃+* k :=
        FiniteField.ringEquivOfCardEq (by simpa [ZMod.card] using hk.symm)
      let : CharP k 11 := charP_of_injective_ringHom (f := e.toRingHom) e.injective 11
      intro h
      have hdvd := (CharP.cast_eq_zero_iff k 11 7).mp h
      omega) hd₂ (by simpa [hk] using hk₂) J b₀ hJ
  refine ⟨b, ?_⟩
  dsimp only at hb
  rw [h₁, h₂] at hb
  norm_num [hk] at hb ⊢
  exact hb

/-- The same actual pointed-Jacobian deduction at forty-one, retaining
geometric Frobenius and the fixed coefficient prime seven. -/
theorem primeFive_pointedJacobian_geometricFrobeniusPolynomial_41
    (k k₂ : Type*) [Field k] [Fintype k] [Field k₂] [Fintype k₂]
    [Algebra k k₂] (hk : Fintype.card k = 41) (hk₂ : Fintype.card k₂ = 1681)
    (hsep : (primeFivePolynomial k).Separable) (h2 : (2 : k) ≠ 0)
    (J : CommGrp (Over (Spec (CommRingCat.of k))))
    (b₀ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
      Over.mk (AlgebraicGeometry.Hyperelliptic.toSpec (primeFivePolynomial k) 3
        (primeFivePolynomial_degree k)))
    (hJ : PointedCurveJacobian k
      (Over.mk (AlgebraicGeometry.Hyperelliptic.toSpec (primeFivePolynomial k) 3
        (primeFivePolynomial_degree k))) b₀ J) :
    ∃ b : Module.Basis (Fin 4) ℚ_[7] (Module.Dual ℚ_[7] (rationalTate k J.X 7)),
      (LinearMap.toMatrix b b
        ((tateRepresentation k J.X 7).dual
          (AlgebraicGeometry.Hyperelliptic.finiteFieldGeometricFrobenius k))).charpolyRev =
        1 + X + 51 * X ^ 2 + 41 * X ^ 3 + 1681 * X ^ 4 := by
  classical
  let f := primeFivePolynomial k
  have hd : f.natDegree = 2 * 3 := primeFivePolynomial_degree k
  have hd₂ : (f.map (algebraMap k k₂)).natDegree = 2 * 3 := by
    simpa only [f, primeFivePolynomial_map] using primeFivePolynomial_degree k₂
  have h₁ : Nat.card (Scheme.RationalPoint
      (AlgebraicGeometry.Hyperelliptic.toSpec f 3 hd)) = 43 := by
    exact (rationalPointCount_congr (plusPolynomial_five k).symm (by decide) hd
      (plusPolynomial_evenDegree 5 (by decide) (125 : k))).trans
        (primeFive_count_of_card_eq_41 hk)
  have h₂ : Nat.card (Scheme.RationalPoint
      (AlgebraicGeometry.Hyperelliptic.toSpec
        (f.map (algebraMap k k₂)) 3 hd₂)) = 1783 := by
    have heq : f.map (algebraMap k k₂) = plusPolynomial 5 (125 : k₂) := by
      simpa only [f, primeFivePolynomial_map] using (plusPolynomial_five k₂).symm
    exact (rationalPointCount_congr heq (by decide) hd₂
      (plusPolynomial_evenDegree 5 (by decide) (125 : k₂))).trans
        (primeFive_count_of_card_eq_1681 hk₂)
  obtain ⟨b, hb⟩ := AlgebraicGeometry.Hyperelliptic.genusTwoPointedJacobian_geometricFrobeniusPolynomial
    k f hd (primeFivePolynomial_monic k) hsep h2 7 (by
      let e : ZMod 41 ≃+* k :=
        FiniteField.ringEquivOfCardEq (by simpa [ZMod.card] using hk.symm)
      let : CharP k 41 := charP_of_injective_ringHom (f := e.toRingHom) e.injective 41
      intro h
      have hdvd := (CharP.cast_eq_zero_iff k 41 7).mp h
      omega) hd₂ (by simpa [hk] using hk₂) J b₀ hJ
  refine ⟨b, ?_⟩
  dsimp only at hb
  rw [h₁, h₂] at hb
  norm_num [hk] at hb ⊢
  exact hb

/-! The following two statements use the conductor coefficient prime five. -/

/-- The actual pointed Jacobian of the reduced level-five curve has the
eleven-prime polynomial under geometric Frobenius on its five-adic cohomological dual
Tate action. The curve count and polynomial are proved, while the general
Abel–Jacobi cohomology comparison remains a visible literature premise. -/
theorem primeFive_pointedJacobian_geometricFrobeniusPolynomial_11_at_five
    (k k₂ : Type*) [Field k] [Fintype k] [Field k₂] [Fintype k₂]
    [Algebra k k₂] (hk : Fintype.card k = 11) (hk₂ : Fintype.card k₂ = 121)
    (hsep : (primeFivePolynomial k).Separable) (h2 : (2 : k) ≠ 0)
    (J : CommGrp (Over (Spec (CommRingCat.of k))))
    (b₀ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
      Over.mk (AlgebraicGeometry.Hyperelliptic.toSpec (primeFivePolynomial k) 3
        (primeFivePolynomial_degree k)))
    (hJ : PointedCurveJacobian k
      (Over.mk (AlgebraicGeometry.Hyperelliptic.toSpec (primeFivePolynomial k) 3
        (primeFivePolynomial_degree k))) b₀ J) :
    ∃ b : Module.Basis (Fin 4) ℚ_[5] (Module.Dual ℚ_[5] (rationalTate k J.X 5)),
      (LinearMap.toMatrix b b
        ((tateRepresentation k J.X 5).dual
          (AlgebraicGeometry.Hyperelliptic.finiteFieldGeometricFrobenius k))).charpolyRev =
        1 + X + 21 * X ^ 2 + 11 * X ^ 3 + 121 * X ^ 4 := by
  classical
  let f := primeFivePolynomial k
  have hd : f.natDegree = 2 * 3 := primeFivePolynomial_degree k
  have hd₂ : (f.map (algebraMap k k₂)).natDegree = 2 * 3 := by
    simpa only [f, primeFivePolynomial_map] using primeFivePolynomial_degree k₂
  have h₁ : Nat.card (Scheme.RationalPoint
      (AlgebraicGeometry.Hyperelliptic.toSpec f 3 hd)) = 13 := by
    exact (rationalPointCount_congr (plusPolynomial_five k).symm (by decide) hd
      (plusPolynomial_evenDegree 5 (by decide) (125 : k))).trans
        (primeFive_count_of_card_eq_11 hk)
  have h₂ : Nat.card (Scheme.RationalPoint
      (AlgebraicGeometry.Hyperelliptic.toSpec
        (f.map (algebraMap k k₂)) 3 hd₂)) = 163 := by
    have heq : f.map (algebraMap k k₂) = plusPolynomial 5 (125 : k₂) := by
      simpa only [f, primeFivePolynomial_map] using (plusPolynomial_five k₂).symm
    exact (rationalPointCount_congr heq (by decide) hd₂
      (plusPolynomial_evenDegree 5 (by decide) (125 : k₂))).trans
        (primeFive_count_of_card_eq_121 hk₂)
  obtain ⟨b, hb⟩ := AlgebraicGeometry.Hyperelliptic.genusTwoPointedJacobian_geometricFrobeniusPolynomial
    k f hd (primeFivePolynomial_monic k) hsep h2 5 (by
      let e : ZMod 11 ≃+* k :=
        FiniteField.ringEquivOfCardEq (by simpa [ZMod.card] using hk.symm)
      let : CharP k 11 := charP_of_injective_ringHom (f := e.toRingHom) e.injective 11
      intro h
      have hdvd := (CharP.cast_eq_zero_iff k 11 5).mp h
      omega) hd₂ (by simpa [hk] using hk₂) J b₀ hJ
  refine ⟨b, ?_⟩
  dsimp only at hb
  rw [h₁, h₂] at hb
  norm_num [hk] at hb ⊢
  exact hb

/-- Choose the full five-adic cohomology basis supplied by the checked
point-count theorem for the actual pointed Jacobian at eleven. -/
def primeFive_pointedJacobianBasis11_at_five
    (k k₂ : Type*) [Field k] [Fintype k] [Field k₂] [Fintype k₂]
    [Algebra k k₂] (hk : Fintype.card k = 11) (hk₂ : Fintype.card k₂ = 121)
    (hsep : (primeFivePolynomial k).Separable) (h2 : (2 : k) ≠ 0)
    (J : CommGrp (Over (Spec (CommRingCat.of k))))
    (b₀ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
      Over.mk (AlgebraicGeometry.Hyperelliptic.toSpec (primeFivePolynomial k) 3
        (primeFivePolynomial_degree k)))
    (hJ : PointedCurveJacobian k
      (Over.mk (AlgebraicGeometry.Hyperelliptic.toSpec (primeFivePolynomial k) 3
        (primeFivePolynomial_degree k))) b₀ J) :
    Module.Basis (Fin 4) ℚ_[5] (Module.Dual ℚ_[5] (rationalTate k J.X 5)) :=
  (primeFive_pointedJacobian_geometricFrobeniusPolynomial_11_at_five
    k k₂ hk hk₂ hsep h2 J b₀ hJ).choose

/-- The chosen basis has the literal eleven-prime polynomial. -/
theorem primeFive_pointedJacobianBasis11_at_five_charpolyRev
    (k k₂ : Type*) [Field k] [Fintype k] [Field k₂] [Fintype k₂]
    [Algebra k k₂] (hk : Fintype.card k = 11) (hk₂ : Fintype.card k₂ = 121)
    (hsep : (primeFivePolynomial k).Separable) (h2 : (2 : k) ≠ 0)
    (J : CommGrp (Over (Spec (CommRingCat.of k))))
    (b₀ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
      Over.mk (AlgebraicGeometry.Hyperelliptic.toSpec (primeFivePolynomial k) 3
        (primeFivePolynomial_degree k)))
    (hJ : PointedCurveJacobian k
      (Over.mk (AlgebraicGeometry.Hyperelliptic.toSpec (primeFivePolynomial k) 3
        (primeFivePolynomial_degree k))) b₀ J) :
    (LinearMap.toMatrix
      (primeFive_pointedJacobianBasis11_at_five k k₂ hk hk₂ hsep h2 J b₀ hJ)
      (primeFive_pointedJacobianBasis11_at_five k k₂ hk hk₂ hsep h2 J b₀ hJ)
      ((tateRepresentation k J.X 5).dual
        (AlgebraicGeometry.Hyperelliptic.finiteFieldGeometricFrobenius k))).charpolyRev =
          primeFiveNumericalPolynomial11 ℚ_[5] := by
  simpa only [primeFiveNumericalPolynomial11, primeFive_pointedJacobianBasis11_at_five] using
    (primeFive_pointedJacobian_geometricFrobeniusPolynomial_11_at_five
      k k₂ hk hk₂ hsep h2 J b₀ hJ).choose_spec

/-- The same actual pointed-Jacobian deduction at forty-one, retaining
geometric Frobenius and the fixed coefficient prime five. -/
theorem primeFive_pointedJacobian_geometricFrobeniusPolynomial_41_at_five
    (k k₂ : Type*) [Field k] [Fintype k] [Field k₂] [Fintype k₂]
    [Algebra k k₂] (hk : Fintype.card k = 41) (hk₂ : Fintype.card k₂ = 1681)
    (hsep : (primeFivePolynomial k).Separable) (h2 : (2 : k) ≠ 0)
    (J : CommGrp (Over (Spec (CommRingCat.of k))))
    (b₀ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
      Over.mk (AlgebraicGeometry.Hyperelliptic.toSpec (primeFivePolynomial k) 3
        (primeFivePolynomial_degree k)))
    (hJ : PointedCurveJacobian k
      (Over.mk (AlgebraicGeometry.Hyperelliptic.toSpec (primeFivePolynomial k) 3
        (primeFivePolynomial_degree k))) b₀ J) :
    ∃ b : Module.Basis (Fin 4) ℚ_[5] (Module.Dual ℚ_[5] (rationalTate k J.X 5)),
      (LinearMap.toMatrix b b
        ((tateRepresentation k J.X 5).dual
          (AlgebraicGeometry.Hyperelliptic.finiteFieldGeometricFrobenius k))).charpolyRev =
        1 + X + 51 * X ^ 2 + 41 * X ^ 3 + 1681 * X ^ 4 := by
  classical
  let f := primeFivePolynomial k
  have hd : f.natDegree = 2 * 3 := primeFivePolynomial_degree k
  have hd₂ : (f.map (algebraMap k k₂)).natDegree = 2 * 3 := by
    simpa only [f, primeFivePolynomial_map] using primeFivePolynomial_degree k₂
  have h₁ : Nat.card (Scheme.RationalPoint
      (AlgebraicGeometry.Hyperelliptic.toSpec f 3 hd)) = 43 := by
    exact (rationalPointCount_congr (plusPolynomial_five k).symm (by decide) hd
      (plusPolynomial_evenDegree 5 (by decide) (125 : k))).trans
        (primeFive_count_of_card_eq_41 hk)
  have h₂ : Nat.card (Scheme.RationalPoint
      (AlgebraicGeometry.Hyperelliptic.toSpec
        (f.map (algebraMap k k₂)) 3 hd₂)) = 1783 := by
    have heq : f.map (algebraMap k k₂) = plusPolynomial 5 (125 : k₂) := by
      simpa only [f, primeFivePolynomial_map] using (plusPolynomial_five k₂).symm
    exact (rationalPointCount_congr heq (by decide) hd₂
      (plusPolynomial_evenDegree 5 (by decide) (125 : k₂))).trans
        (primeFive_count_of_card_eq_1681 hk₂)
  obtain ⟨b, hb⟩ := AlgebraicGeometry.Hyperelliptic.genusTwoPointedJacobian_geometricFrobeniusPolynomial
    k f hd (primeFivePolynomial_monic k) hsep h2 5 (by
      let e : ZMod 41 ≃+* k :=
        FiniteField.ringEquivOfCardEq (by simpa [ZMod.card] using hk.symm)
      let : CharP k 41 := charP_of_injective_ringHom (f := e.toRingHom) e.injective 41
      intro h
      have hdvd := (CharP.cast_eq_zero_iff k 41 5).mp h
      omega) hd₂ (by simpa [hk] using hk₂) J b₀ hJ
  refine ⟨b, ?_⟩
  dsimp only at hb
  rw [h₁, h₂] at hb
  norm_num [hk] at hb ⊢
  exact hb

/-- Choose the full five-adic cohomology basis supplied by the checked
point-count theorem for the actual pointed Jacobian at forty-one. -/
def primeFive_pointedJacobianBasis41_at_five
    (k k₂ : Type*) [Field k] [Fintype k] [Field k₂] [Fintype k₂]
    [Algebra k k₂] (hk : Fintype.card k = 41) (hk₂ : Fintype.card k₂ = 1681)
    (hsep : (primeFivePolynomial k).Separable) (h2 : (2 : k) ≠ 0)
    (J : CommGrp (Over (Spec (CommRingCat.of k))))
    (b₀ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
      Over.mk (AlgebraicGeometry.Hyperelliptic.toSpec (primeFivePolynomial k) 3
        (primeFivePolynomial_degree k)))
    (hJ : PointedCurveJacobian k
      (Over.mk (AlgebraicGeometry.Hyperelliptic.toSpec (primeFivePolynomial k) 3
        (primeFivePolynomial_degree k))) b₀ J) :
    Module.Basis (Fin 4) ℚ_[5] (Module.Dual ℚ_[5] (rationalTate k J.X 5)) :=
  (primeFive_pointedJacobian_geometricFrobeniusPolynomial_41_at_five
    k k₂ hk hk₂ hsep h2 J b₀ hJ).choose

/-- The chosen basis has the literal forty-one-prime polynomial. -/
theorem primeFive_pointedJacobianBasis41_at_five_charpolyRev
    (k k₂ : Type*) [Field k] [Fintype k] [Field k₂] [Fintype k₂]
    [Algebra k k₂] (hk : Fintype.card k = 41) (hk₂ : Fintype.card k₂ = 1681)
    (hsep : (primeFivePolynomial k).Separable) (h2 : (2 : k) ≠ 0)
    (J : CommGrp (Over (Spec (CommRingCat.of k))))
    (b₀ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
      Over.mk (AlgebraicGeometry.Hyperelliptic.toSpec (primeFivePolynomial k) 3
        (primeFivePolynomial_degree k)))
    (hJ : PointedCurveJacobian k
      (Over.mk (AlgebraicGeometry.Hyperelliptic.toSpec (primeFivePolynomial k) 3
        (primeFivePolynomial_degree k))) b₀ J) :
    (LinearMap.toMatrix
      (primeFive_pointedJacobianBasis41_at_five k k₂ hk hk₂ hsep h2 J b₀ hJ)
      (primeFive_pointedJacobianBasis41_at_five k k₂ hk hk₂ hsep h2 J b₀ hJ)
      ((tateRepresentation k J.X 5).dual
        (AlgebraicGeometry.Hyperelliptic.finiteFieldGeometricFrobenius k))).charpolyRev =
          primeFiveNumericalPolynomial41 ℚ_[5] := by
  simpa only [primeFiveNumericalPolynomial41, primeFive_pointedJacobianBasis41_at_five] using
    (primeFive_pointedJacobian_geometricFrobeniusPolynomial_41_at_five
      k k₂ hk hk₂ hsep h2 J b₀ hJ).choose_spec

end HilbertModularity.Examples
