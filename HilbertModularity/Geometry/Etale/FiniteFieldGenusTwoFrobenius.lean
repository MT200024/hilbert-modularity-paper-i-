/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.Cohomology.Galois
public import HilbertModularity.Geometry.HyperellipticPoints
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-! # Frobenius on a smooth genus-two curve over a finite field

The sole admitted result below is the standard Lefschetz trace formula and
Poincaré-duality functional equation for the actual geometric cohomology of
an even-degree hyperelliptic curve. It is stated before any level-five point
counts or real-multiplication labels are inserted.
-/

public noncomputable section

open CategoryTheory Limits Polynomial
open AlgebraicGeometry.GroupScheme

namespace AlgebraicGeometry.Hyperelliptic

variable (k : Type*) [Field k] [Fintype k]

/-- The inverse of arithmetic field Frobenius is geometric field Frobenius.
The rational cohomology action below uses this element, without a Tate twist. -/
def finiteFieldGeometricFrobenius :
    AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k :=
  (FiniteField.frobeniusAlgEquivOfAlgebraic k (AlgebraicClosure k))⁻¹

variable (f : k[X]) (hdeg : f.natDegree = 2 * 3) (ℓ : ℕ) [Fact ℓ.Prime]

/-- Actual rational pro-étale cohomology of the geometric genus-two completion. -/
abbrev genusTwoGeometricH1 :=
  (pullback (fieldPoint k (AlgebraicClosure k)).hom (toSpec f 3 hdeg)).RationalEllAdicCohomology ℓ 1

/-- Geometric Frobenius on the actual first cohomology of this curve. -/
def genusTwoGeometricFrobeniusAction :
    genusTwoGeometricH1 k f hdeg ℓ →ₗ[ℚ_[ℓ]] genusTwoGeometricH1 k f hdeg ℓ :=
  Scheme.rationalEllAdicCohomologyGaloisRepresentation k (toSpec f 3 hdeg) ℓ 1
    (finiteFieldGeometricFrobenius k)

/-- The named Frobenius action is the actual rational cohomology Galois action
at inverse arithmetic field Frobenius. -/
theorem genusTwoGeometricFrobeniusAction_eq :
    genusTwoGeometricFrobeniusAction k f hdeg ℓ =
      Scheme.rationalEllAdicCohomologyGaloisRepresentation k (toSpec f 3 hdeg) ℓ 1
        (finiteFieldGeometricFrobenius k) := (rfl)

/-- [src_milne_lec, Theorem 25.1, Proposition 27.3, Theorem 27.6,
Remark 27.7, Theorem 27.12, Propositions 29.10 and 29.12, printed pp.145–168]
gives the first two power traces, the functional equation and the relation
between geometric Galois Frobenius and pullback by the q-power morphism.
[src_poonen_curves, §2.8.1, printed pp.36–37] gives genus two for a monic
separable degree-six branch polynomial in odd characteristic.
[proetale2015, Lemma 6.8.2(1) and Proposition 6.8.4(1), printed pp.58–59;
Corollary 5.1.5] identifies the continuous-coefficient pro-étale construction
with the usual ℓ-adic system; the connected curve has surjective constant
H⁰ reduction maps, so the degree-one inverse-limit term vanishes. The
quadratic-field count uses the mapped equation of the same curve. This is a
standard composite input, not a verbatim theorem of any one source. It
asserts no numerical count or labelled real-multiplication factor. -/
theorem genusTwoGeometricFrobeniusPolynomial
    {k₂ : Type*} [Field k₂] [Fintype k₂] [Algebra k k₂]
    (hf : f.Monic) (hsep : f.Separable) (h2 : (2 : k) ≠ 0)
    (hℓ : (ℓ : k) ≠ 0)
    (hdeg₂ : (f.map (algebraMap k k₂)).natDegree = 2 * 3)
    (hcard₂ : Fintype.card k₂ = (Fintype.card k) ^ 2) :
    ∃ b : Module.Basis (Fin 4) ℚ_[ℓ] (genusTwoGeometricH1 k f hdeg ℓ),
      let q : ℚ_[ℓ] := Fintype.card k
      let s₁ : ℚ_[ℓ] := q + 1 - Nat.card (Scheme.RationalPoint (toSpec f 3 hdeg))
      let s₂ : ℚ_[ℓ] := q ^ 2 + 1 -
        Nat.card (Scheme.RationalPoint (toSpec (f.map (algebraMap k k₂)) 3 hdeg₂))
      (LinearMap.toMatrix b b (genusTwoGeometricFrobeniusAction k f hdeg ℓ)).charpolyRev =
        1 - C s₁ * X + C ((s₁ ^ 2 - s₂) / 2) * X ^ 2 -
          C (q * s₁) * X ^ 3 + C (q ^ 2) * X ^ 4 := by
  sorry

end AlgebraicGeometry.Hyperelliptic
