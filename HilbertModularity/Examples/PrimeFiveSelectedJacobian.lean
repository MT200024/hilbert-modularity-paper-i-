/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Examples.PrimeFiveJacobianPolynomial
public import HilbertModularity.Geometry.GroupScheme.PrimeGoodSpecialization

/-! # The special fibre of the selected level-five Jacobian

The original selected plus family and its integral equation are retained.
The standard relative Jacobian input identifies the special fibre of one
good model with the pointed Jacobian of the actual reduced completed curve.
-/

public noncomputable section

open CategoryTheory Polynomial AlgebraicGeometry IsDedekindDomain
open scoped NumberField

namespace HilbertModularity.Examples

open Hyperelliptic Hypergeometric _root_.HilbertModularity.Cyclotomic GroupScheme

attribute [local instance] Ideal.Quotient.field
local instance primeFiveSelectedPrime5 : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The manuscript's rational parameter in the actual real coefficient field. -/
def primeFiveParameter : ProjectiveLine.Parameter (realCyclotomicField 5) :=
  ⟨125, by norm_num, by norm_num⟩

@[simp] theorem primeFiveParameter_val : primeFiveParameter.val = 125 := (rfl)

private theorem hyperellipticToSpec_over_congr
    {k : Type*} [Field k] {f g : k[X]} {n m : ℕ}
    (h : f = g) (hn : n = m)
    (hf : f.natDegree = 2 * n) (hg : g.natDegree = 2 * m) :
    Over.mk (AlgebraicGeometry.Hyperelliptic.toSpec f n hf) =
      Over.mk (AlgebraicGeometry.Hyperelliptic.toSpec g m hg) := by
  cases h
  cases hn
  rfl

/-- The selected plus fibre at the fixed level-five parameter has a good
model whose special fibre is the pointed Jacobian of the *reduced plus
curve*. The old good-reduction API is preserved by projection of the richer
standard literature theorem. No independent model or numeric polynomial is
admitted here. -/
theorem exists_primeFive_selectedSpecialPlusJacobian
    (P : HeightOneSpectrum (𝓞 (realCyclotomicField 5)))
    (h2 : (2 : 𝓞 (realCyclotomicField 5)) ∉ P.asIdeal)
    (hsep : (primeFivePolynomial (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal)).Separable) :
    let K := realCyclotomicField 5
    let R := P.valuationSubringAtPrime K
    let k := 𝓞 K ⧸ P.asIdeal
    let f₀ := plusPolynomial 5 (125 : R)
    let hdegree₀ : f₀.natDegree = 2 * ((5 + 1) / 2) := by
      simpa only [f₀] using
        (plusPolynomial_isMonicOfDegree 5 (by decide) (125 : R)).natDegree_eq
    let fₛ := f₀.map (P.localResidue (K := K))
    let hdegreeₛ : fₛ.natDegree = 2 * ((5 + 1) / 2) :=
      hyperellipticReducedPolynomial_degree K P ((5 + 1) / 2) f₀
        (plusPolynomial_isMonicOfDegree 5 (by decide) (125 : R)).monic hdegree₀
    ∃ (B : CommGrp (Over (Spec (CommRingCat.of R)))),
      IsProper B.X.hom ∧ Smooth B.X.hom ∧ GeometricallyConnected B.X.hom ∧
        Nonempty (primePlusFiber 5 (by decide) primeFiveParameter ≅
          localGenericFiber K P B) ∧
        ∃ bₛ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
          Over.mk (AlgebraicGeometry.Hyperelliptic.toSpec fₛ ((5 + 1) / 2) hdegreeₛ),
          Nonempty (PointedCurveJacobian k
            (Over.mk (AlgebraicGeometry.Hyperelliptic.toSpec
              fₛ ((5 + 1) / 2) hdegreeₛ)) bₛ (localSpecialFiber K P B)) := by
  let K := realCyclotomicField 5
  let R := P.valuationSubringAtPrime K
  let k := 𝓞 K ⧸ P.asIdeal
  let f₀ := plusPolynomial 5 (125 : R)
  have hmonic : f₀.Monic := (plusPolynomial_isMonicOfDegree 5 (by decide) (125 : R)).monic
  have hdegree : f₀.natDegree = 2 * ((5 + 1) / 2) := by
    simpa only [f₀] using
      (plusPolynomial_isMonicOfDegree 5 (by decide) (125 : R)).natDegree_eq
  have hgeneric : f₀.map (algebraMap R K) = plusPolynomial 5 (125 : K) := by
    simp only [f₀, plusPolynomial_map, map_ofNat]
  have hsep₀ : (f₀.map (P.localResidue (K := K))).Separable := by
    change ((plusPolynomial 5 (125 : R)).map (P.localResidue (K := K))).Separable
    rw [plusPolynomial_map, map_ofNat, plusPolynomial_five]
    exact hsep
  let hJ := (primePlusFiberJacobian 5 (by decide) primeFiveParameter).transport (Iso.refl _)
  exact exists_hyperellipticJacobian_goodReduction_withSpecialFiber
    K P ((5 + 1) / 2) (by decide)
    (plusPolynomial 5 (125 : K)) (plusPolynomial_evenDegree 5 (by decide) (125 : K))
    f₀ hmonic hdegree hgeneric h2 hsep₀
    (plusBranchOver 5 (by decide) (125 : K))
    (primePlusFiber 5 (by decide) primeFiveParameter) hJ

/-- The special fibre just obtained is the pointed Jacobian of the exact
displayed level-five polynomial in its residue field. -/
theorem exists_primeFive_selectedSpecialJacobian
    (P : HeightOneSpectrum (𝓞 (realCyclotomicField 5)))
    (h2 : (2 : 𝓞 (realCyclotomicField 5)) ∉ P.asIdeal)
    (hsep : (primeFivePolynomial (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal)).Separable) :
    let K := realCyclotomicField 5
    let k := 𝓞 K ⧸ P.asIdeal
    ∃ (B : CommGrp (Over (Spec (CommRingCat.of (P.valuationSubringAtPrime K))))),
      IsProper B.X.hom ∧ Smooth B.X.hom ∧ GeometricallyConnected B.X.hom ∧
        Nonempty (primePlusFiber 5 (by decide) primeFiveParameter ≅
          localGenericFiber K P B) ∧
        ∃ bₛ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
          Over.mk (AlgebraicGeometry.Hyperelliptic.toSpec
            (primeFivePolynomial k) 3 (primeFivePolynomial_degree k)),
          Nonempty (PointedCurveJacobian k
            (Over.mk (AlgebraicGeometry.Hyperelliptic.toSpec
              (primeFivePolynomial k) 3 (primeFivePolynomial_degree k)))
            bₛ (localSpecialFiber K P B)) := by
  let K := realCyclotomicField 5
  let R := P.valuationSubringAtPrime K
  let k := 𝓞 K ⧸ P.asIdeal
  let f₀ := plusPolynomial 5 (125 : R)
  have hmonic : f₀.Monic := (plusPolynomial_isMonicOfDegree 5 (by decide) (125 : R)).monic
  have hdegree : f₀.natDegree = 2 * ((5 + 1) / 2) := by
    simpa only [f₀] using
      (plusPolynomial_isMonicOfDegree 5 (by decide) (125 : R)).natDegree_eq
  obtain ⟨B, hproper, hsmooth, hconnected, he, bₛ, ⟨hJₛ⟩⟩ :=
    exists_primeFive_selectedSpecialPlusJacobian P h2 hsep
  have hred : f₀.map (P.localResidue (K := K)) = primeFivePolynomial k := by
    change (plusPolynomial 5 (125 : R)).map (P.localResidue (K := K)) = _
    rw [plusPolynomial_map, map_ofNat, plusPolynomial_five]
  let eₛ : Over.mk (AlgebraicGeometry.Hyperelliptic.toSpec
      (primeFivePolynomial k) 3 (primeFivePolynomial_degree k)) ≅
      Over.mk (AlgebraicGeometry.Hyperelliptic.toSpec
        (f₀.map (P.localResidue (K := K))) ((5 + 1) / 2)
        (hyperellipticReducedPolynomial_degree K P ((5 + 1) / 2) f₀ hmonic hdegree)) :=
    eqToIso (hyperellipticToSpec_over_congr hred.symm (by decide)
      (primeFivePolynomial_degree k)
      (hyperellipticReducedPolynomial_degree K P ((5 + 1) / 2) f₀ hmonic hdegree))
  exact ⟨B, hproper, hsmooth, hconnected, he,
    bₛ ≫ eₛ.inv, ⟨hJₛ.transport eₛ⟩⟩

end HilbertModularity.Examples
