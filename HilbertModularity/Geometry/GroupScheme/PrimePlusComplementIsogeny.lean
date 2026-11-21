/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.PrimePlusDarmonMestreJacobian
public import HilbertModularity.Geometry.TateModule.FiniteIsogeny
public import HilbertModularity.Geometry.ProjectiveInvolution
public import HilbertModularity.NumberTheory.RealCyclotomicQuadratic
public import HilbertModularity.NumberTheory.RealCyclotomicPrime

/-! # Darmon–Mestre's complementary parameter on the selected plus family

For `C₂(s)` in [DarmonMestre, Proposition 2.3, printed pp. 307–308], the
manuscript's plus parameter is `s = 2ξ - 1`; replacing `ξ` by `1 - ξ`
replaces `s` by `-s`. The source correspondence is an isogeny between these
two Jacobians over the full cyclotomic field. Its arithmetic descent and
the resulting Tate twist are separate from this parameter identity.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial
open HilbertModularity.Cyclotomic HilbertModularity.Hyperelliptic
open scoped NumberField

namespace HilbertModularity.Hypergeometric

/-- Darmon–Mestre's parameter `s` for the selected plus curve. -/
def darmonMestreParameter {K : Type*} [CommRing K] (t : K) : K := 2 * t - 1

/-- The rational complement sends Darmon–Mestre's `s` to `-s`. -/
theorem darmonMestreParameter_complement {K : Type*} [CommRing K] (t : K) :
    darmonMestreParameter (1 - t) = -darmonMestreParameter t := by
  simp only [darmonMestreParameter]
  ring

/-- The source curve `C₂(-s)` is exactly the plus curve at `1-t`.
This is the equation-level specialization of Proposition 2.3; it does not
assert a Jacobian or a Galois representation comparison. -/
theorem darmonMestreComplementPolynomial_eq_plusPolynomial
    {K : Type*} [Field K] (p : ℕ) (t : K) :
    darmonMestrePlusPolynomial (Chebyshev.C K p)
      (-darmonMestreParameter t) = plusPolynomial p (1 - t) := by
  rw [← darmonMestreParameter_complement t]
  exact darmonMestrePlusPolynomial_eq_plusPolynomial p (1 - t)

/-- The actual punctured parameter at the complementary cusp is carried to
the negative Darmon–Mestre parameter, over the same real cyclotomic field. -/
theorem darmonMestreParameter_complementPoint
    (p : ℕ) [Fact p.Prime]
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p)) :
    darmonMestreParameter
      (ProjectiveLine.complementParameter (realCyclotomicField p) ξ).val =
        -darmonMestreParameter ξ.val := by
  rw [ProjectiveLine.complementParameter_val]
  exact darmonMestreParameter_complement ξ.val

/-- Both sides of Darmon–Mestre's correspondence are pointed Jacobians of
the actual selected prime plus family. The first curve is `C₂(s)` and the
second is `C₂(-s)` by `darmonMestreParameter_complementPoint`; the target
abelian varieties retain their already chosen real-multiplication actions.
-/
def primePlusDarmonMestreComplementJacobianPair
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p)) :=
  (primePlusDarmonMestreRationalFiberJacobian p hp ξ,
    primePlusDarmonMestreRationalFiberJacobian p hp
      (ProjectiveLine.complementParameter (realCyclotomicField p) ξ))

/-- Base change of the *selected* pointed plus Jacobian at `ξ` from the real
cyclotomic field to the full cyclotomic field. Darmon--Mestre's correspondence
is defined over this latter field, since it uses the rotation by `ζ^a`. -/
def primePlusFullCyclotomicJacobian
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p)) :
    CommGrp (Over (Spec (CommRingCat.of (cyclotomicField p)))) := by
  letI : Algebra (realCyclotomicField p) (cyclotomicField p) := realFieldAlgebra p
  exact
  (Over.pullback (Spec.map (CommRingCat.ofHom
    (algebraMap (realCyclotomicField p) (cyclotomicField p))))).mapCommGrp.obj
    (GroupScheme.fiber (realCyclotomicField p) (primePlusFamily p hp)
      (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ))

/-- Specialize a selected family endomorphism, then extend scalars to the
full cyclotomic field. This API keeps the base-change object encapsulated. -/
def primePlusFullCyclotomicFiberEndomorphism
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (f : End (primePlusFamily p hp)) :
    End (primePlusFullCyclotomicJacobian p hp ξ) := by
  letI : Algebra (realCyclotomicField p) (cyclotomicField p) := realFieldAlgebra p
  exact (Over.pullback (Spec.map (CommRingCat.ofHom
    (algebraMap (realCyclotomicField p) (cyclotomicField p))))).mapCommGrp.map
      (GroupScheme.fiberEndomorphismMap (realCyclotomicField p)
        (primePlusFamily p hp)
        (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ) f)

/-- The rational Tate action of an endomorphism on one full cyclotomic
base-changed selected fibre. -/
def primePlusFullCyclotomicTateEndomorphism
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (f : End (primePlusFullCyclotomicJacobian p hp ξ)) :
    Module.End ℚ_[p] (GroupScheme.rationalTate (cyclotomicField p)
      (primePlusFullCyclotomicJacobian p hp ξ).X p) :=
  GroupScheme.rationalTateMap (cyclotomicField p) p f.hom.hom.hom

/-- One fixed geometric correspondence, with its source RM normalization
kept visible. [DarmonMestre, Proposition 2.3, printed pp. 307--308] gives
the degree-`p` maps and composition `ω-2 = -realPrimeGenerator p`. The
correspondence is over the full cyclotomic field and its source RM action is
separate from the selected family's action. -/
structure PrimePlusDarmonMestreGeometricData
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p)) where
  sourceRM : 𝓞 (realCyclotomicField p) →+*
    End (primePlusFullCyclotomicJacobian p hp ξ)
  eta : primePlusFullCyclotomicJacobian p hp ξ ⟶
    primePlusFullCyclotomicJacobian p hp
      (ProjectiveLine.complementParameter (realCyclotomicField p) ξ)
  etaBack : primePlusFullCyclotomicJacobian p hp
      (ProjectiveLine.complementParameter (realCyclotomicField p) ξ) ⟶
    primePlusFullCyclotomicJacobian p hp ξ
  etaFinite : IsFinite eta.hom.hom.hom.left
  etaSurjective : Surjective eta.hom.hom.hom.left
  etaBackFinite : IsFinite etaBack.hom.hom.hom.left
  etaBackSurjective : Surjective etaBack.hom.hom.hom.left
  kernelCard : Nat.card (GroupScheme.pointsMap (cyclotomicField p)
    (AlgebraicClosure (cyclotomicField p)) eta.hom.hom.hom).ker = p
  composition : eta ≫ etaBack = sourceRM (-realPrimeGenerator p)

/-- The actual Darmon--Mestre map becomes a rational `p`-adic Tate
equivalence between the same two plus Jacobians after passage to the full
cyclotomic field. Inverting degree `p` here is valid over `ℚₚ`; the source's
later auxiliary-prime restriction applies to finite torsion, not rational Tate.
-/
theorem primePlusComplement_fullCyclotomicTateEquiv
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (I : PrimePlusDarmonMestreGeometricData p hp ξ) :
    Nonempty ((GroupScheme.tateRepresentation (cyclotomicField p)
      (primePlusFullCyclotomicJacobian p hp ξ).X p).Equiv
      (GroupScheme.tateRepresentation (cyclotomicField p)
        (primePlusFullCyclotomicJacobian p hp
          (ProjectiveLine.complementParameter (realCyclotomicField p) ξ)).X p)) := by
  let : IsFinite I.eta.hom.hom.hom.left := I.etaFinite
  let : Surjective I.eta.hom.hom.hom.left := I.etaSurjective
  exact ⟨GroupScheme.tateFiniteSurjectiveEquiv (cyclotomicField p)
    I.eta.hom.hom.hom p⟩

end HilbertModularity.Hypergeometric
