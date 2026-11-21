/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hyperelliptic.SpecialFiberNodeCoordinates
public import HilbertModularity.Hyperelliptic.Projective
public import Mathlib.AlgebraicGeometry.Spec

/-! # Node coordinates in the scaled family

The special-fibre identity `UV = 0` does not describe an étale chart of the
whole family.  For the actual finite chart `W² = u²P(u)² - 4Tu`, the linear
coordinates `W ± uP(u)` have product `-4Tu`.  At a nonzero residue root, `u`
is a unit and the smoothing parameter is `-4T`.  At `u = 0`, a different
change of coordinates gives smoothing parameter `-4T²`.  The latter identity
is essential when applying a relative nodal-curve criterion.
-/

public noncomputable section

open Polynomial AlgebraicGeometry
open scoped QuadraticAlgebra

namespace HilbertModularity.Hyperelliptic

variable {S : Type*} [CommRing S]

/-- The first whole-family node coordinate for `W² = h² - 4tu`. -/
def familyNodeMinus (h t u : S) : QuadraticAlgebra S (h ^ 2 - 4 * t * u) 0 :=
  QuadraticAlgebra.omega - algebraMap S _ h

/-- The second whole-family node coordinate for `W² = h² - 4tu`. -/
def familyNodePlus (h t u : S) : QuadraticAlgebra S (h ^ 2 - 4 * t * u) 0 :=
  QuadraticAlgebra.omega + algebraMap S _ h

/-- The smoothing equation before localizing at a nonzero branch point. -/
theorem familyNodeMinus_mul_familyNodePlus (h t u : S) :
    familyNodeMinus h t u * familyNodePlus h t u =
      algebraMap S _ (-(4 * t * u)) := by
  have hω :
      (QuadraticAlgebra.omega : QuadraticAlgebra S (h ^ 2 - 4 * t * u) 0) ^ 2 =
        algebraMap S _ (h ^ 2 - 4 * t * u) := by
    calc
      _ = (QuadraticAlgebra.omega : QuadraticAlgebra S (h ^ 2 - 4 * t * u) 0) *
          QuadraticAlgebra.omega := by ring
      _ = _ := by simp only [QuadraticAlgebra.omega_mul_omega_eq_algebraMap,
        map_zero, zero_mul, add_zero]
  calc
    _ = (QuadraticAlgebra.omega : QuadraticAlgebra S (h ^ 2 - 4 * t * u) 0) ^ 2 -
        (algebraMap S _ h) ^ 2 := by
          simp only [familyNodeMinus, familyNodePlus]
          ring
    _ = _ := by
      rw [hω, ← map_pow, ← map_sub]
      congr 1; ring

/-- Translating the square-root generator identifies the actual family
quadratic algebra with the presentation `Y (Y - 2h) = -4tu`.  This is an
isomorphism over the original coefficient ring, before any localization. -/
def familyNodeTranslatedEquiv (h t u : S) :
    QuadraticAlgebra S (h ^ 2 - 4 * t * u) 0 ≃ₐ[S]
      QuadraticAlgebra S (-(4 * t * u)) (2 * h) :=
  (QuadraticAlgebra.changeGeneratorEquiv (h ^ 2 - 4 * t * u) 0
    (1 : Sˣ) h (by simp) (by simp)).symm

/-- The translated generator is the actual positive linear coordinate. -/
theorem familyNodeTranslatedEquiv_symm_omega (h t u : S) :
    (familyNodeTranslatedEquiv h t u).symm
      (QuadraticAlgebra.omega : QuadraticAlgebra S (-(4 * t * u)) (2 * h)) =
      familyNodePlus h t u := by
  simp [familyNodeTranslatedEquiv, familyNodePlus,
    QuadraticAlgebra.changeGeneratorEquiv_apply,
    QuadraticAlgebra.changeGenerator_omega, Algebra.smul_def]

/-- If `u` is invertible, scaling the second coordinate gives the uniform
nonzero-branch smoothing equation `U V = -4T`.  The map is an actual algebra
coordinate on this open; no regularity of the total space is inferred. -/
theorem familyNonzeroNode_product (h t : S) (u : Sˣ) :
    familyNodeMinus h t (u : S) *
      (familyNodePlus h t (u : S) *
        algebraMap S (QuadraticAlgebra S (h ^ 2 - 4 * t * (u : S)) 0) (↑u⁻¹ : S)) =
      algebraMap S _ (-(4 * t)) := by
  rw [← mul_assoc, familyNodeMinus_mul_familyNodePlus, ← map_mul]
  congr 1
  simp [mul_assoc]

/-- At the zero branch point, multiplication by `P(u)` and the coordinate
`z = uP(u)²` make the two branch sections symmetric about `2T`. -/
def familyZeroNodeMinus (q u t : S) :
    QuadraticAlgebra S ((u * q) ^ 2 - 4 * t * u) 0 :=
  QuadraticAlgebra.omega * algebraMap S _ q -
    algebraMap S _ (u * q ^ 2 - 2 * t)

/-- The opposite coordinate at the zero branch point. -/
def familyZeroNodePlus (q u t : S) :
    QuadraticAlgebra S ((u * q) ^ 2 - 4 * t * u) 0 :=
  QuadraticAlgebra.omega * algebraMap S _ q +
    algebraMap S _ (u * q ^ 2 - 2 * t)

/-- The whole-family equation at `u = 0` has smoothing thickness `T²`.
This is a ring identity and does not claim that these coordinates are étale. -/
theorem familyZeroNodeMinus_mul_familyZeroNodePlus (q u t : S) :
    familyZeroNodeMinus q u t * familyZeroNodePlus q u t =
      algebraMap S _ (-(4 * t ^ 2)) := by
  have hω :
      (QuadraticAlgebra.omega : QuadraticAlgebra S ((u * q) ^ 2 - 4 * t * u) 0) ^ 2 =
        algebraMap S _ ((u * q) ^ 2 - 4 * t * u) := by
    calc
      _ = (QuadraticAlgebra.omega : QuadraticAlgebra S ((u * q) ^ 2 - 4 * t * u) 0) *
          QuadraticAlgebra.omega := by ring
      _ = _ := by simp only [QuadraticAlgebra.omega_mul_omega_eq_algebraMap,
        map_zero, zero_mul, add_zero]
  calc
    _ = ((QuadraticAlgebra.omega : QuadraticAlgebra S ((u * q) ^ 2 - 4 * t * u) 0) *
          algebraMap S _ q) ^ 2 - (algebraMap S _ (u * q ^ 2 - 2 * t)) ^ 2 := by
        simp only [familyZeroNodeMinus, familyZeroNodePlus]
        ring
    _ = _ := by
      calc
        _ = (QuadraticAlgebra.omega :
              QuadraticAlgebra S ((u * q) ^ 2 - 4 * t * u) 0) ^ 2 *
              (algebraMap S _ q) ^ 2 -
              (algebraMap S _ (u * q ^ 2 - 2 * t)) ^ 2 := by ring
        _ = _ := by
          rw [hω, ← map_pow]
          simp only [map_mul, map_sub, map_pow, map_neg]
          simp only [map_ofNat]
          ring_nf

/-- The quadratic algebra for the zero-crossing node chart. Its generator is
`Y = P(u) W`, and its discriminant is `(u P(u)² - 2T)² - 4T²`. -/
abbrev familyZeroNodeAlgebra (q u t : S) :=
  QuadraticAlgebra S ((u * q ^ 2 - 2 * t) ^ 2 - 4 * t ^ 2) 0

/-- The actual zero-crossing chart map sends the node generator `Y` to
`P(u) W`. It is defined before localization; it becomes an equivalence on
the open where `P(u)` is a unit. -/
def familyZeroNodeCoordinateHom (q u t : S) :
    familyZeroNodeAlgebra q u t →ₐ[S]
      QuadraticAlgebra S ((u * q) ^ 2 - 4 * t * u) 0 :=
  QuadraticAlgebra.lift ⟨QuadraticAlgebra.omega *
    algebraMap S _ q, by
      simp only [zero_smul, add_zero]
      apply QuadraticAlgebra.ext <;>
        simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul];
        ring⟩

/-- When `P(u)` is a unit, the zero-crossing coordinate change is an
isomorphism of the actual quadratic algebras, before passing to schemes. -/
def familyZeroNodeCoordinateEquiv (q : Sˣ) (u t : S) :
    familyZeroNodeAlgebra (q : S) u t ≃ₐ[S]
      QuadraticAlgebra S ((u * (q : S)) ^ 2 - 4 * t * u) 0 :=
  QuadraticAlgebra.changeGeneratorEquiv
    ((u * (q : S)) ^ 2 - 4 * t * u) 0 q 0 (by ring) (by ring)

/-- The equivalence sends the node generator to the actual family generator
times the unit `P(u)`. -/
theorem familyZeroNodeCoordinateEquiv_omega (q : Sˣ) (u t : S) :
    familyZeroNodeCoordinateEquiv q u t
      (QuadraticAlgebra.omega : familyZeroNodeAlgebra (q : S) u t) =
      (QuadraticAlgebra.omega :
        QuadraticAlgebra S ((u * (q : S)) ^ 2 - 4 * t * u) 0) *
        algebraMap S _ (q : S) := by
  simp [familyZeroNodeCoordinateEquiv,
    QuadraticAlgebra.changeGeneratorEquiv_apply,
    QuadraticAlgebra.changeGenerator_omega, Algebra.smul_def, mul_comm]

/-- The previously constructed map is the underlying map of this
equivalence wherever the branch factor is invertible. -/
theorem familyZeroNodeCoordinateHom_eq_equiv (q : Sˣ) (u t : S) :
    familyZeroNodeCoordinateHom (q : S) u t =
      (familyZeroNodeCoordinateEquiv q u t).toAlgHom := by
  apply QuadraticAlgebra.algHom_ext
  simpa [familyZeroNodeCoordinateHom] using
    (familyZeroNodeCoordinateEquiv_omega q u t).symm

/-- The zero-crossing coordinate change gives an isomorphism of affine
schemes on every open where `P(u)` is a unit. Its inverse is induced by the
algebra equivalence, so this is a morphism of the actual family chart. -/
def familyZeroNodeCoordinateSpecIso (q : Sˣ) (u t : S) :
    Spec (CommRingCat.of
      (QuadraticAlgebra S ((u * (q : S)) ^ 2 - 4 * t * u) 0)) ≅
    Spec (CommRingCat.of (familyZeroNodeAlgebra (q : S) u t)) :=
  Scheme.Spec.mapIso
    (familyZeroNodeCoordinateEquiv q u t).toRingEquiv.toCommRingCatIso.op

/-- The scheme isomorphism is induced by the explicit coordinate homomorphism. -/
theorem familyZeroNodeCoordinateSpecIso_hom (q : Sˣ) (u t : S) :
    (familyZeroNodeCoordinateSpecIso q u t).hom =
      Spec.map (CommRingCat.ofHom
        (familyZeroNodeCoordinateHom (q : S) u t).toRingHom) := by
  rw [familyZeroNodeCoordinateHom_eq_equiv]
  rfl

/-- The node chart's two linear coordinates map to the actual pair at the
zero crossing. In particular their product is `-4T²` on this family. -/
theorem familyZeroNodeCoordinateHom_minus (q u t : S) :
    familyZeroNodeCoordinateHom q u t
      (QuadraticAlgebra.omega -
        algebraMap S (familyZeroNodeAlgebra q u t) (u * q ^ 2 - 2 * t)) =
      familyZeroNodeMinus q u t := by
  have hω : familyZeroNodeCoordinateHom q u t
      (QuadraticAlgebra.omega : familyZeroNodeAlgebra q u t) =
      (QuadraticAlgebra.omega : QuadraticAlgebra S ((u * q) ^ 2 - 4 * t * u) 0) *
        algebraMap S _ q := by
    simp [familyZeroNodeCoordinateHom]
  simp only [map_sub, AlgHom.commutes, hω, familyZeroNodeMinus]

theorem familyZeroNodeCoordinateHom_plus (q u t : S) :
    familyZeroNodeCoordinateHom q u t
      (QuadraticAlgebra.omega +
        algebraMap S (familyZeroNodeAlgebra q u t) (u * q ^ 2 - 2 * t)) =
      familyZeroNodePlus q u t := by
  have hω : familyZeroNodeCoordinateHom q u t
      (QuadraticAlgebra.omega : familyZeroNodeAlgebra q u t) =
      (QuadraticAlgebra.omega : QuadraticAlgebra S ((u * q) ^ 2 - 4 * t * u) 0) *
        algebraMap S _ q := by
    simp [familyZeroNodeCoordinateHom]
  simp only [map_add, AlgHom.commutes, hω, familyZeroNodePlus]

/-- The generic family coordinate identities use exactly the defining polynomial
of the finite chart of `scaledDoubleCover`, not a second quadratic family. -/
theorem finiteBranchPolynomial_eq_nodeEquation (P : S[X]) (t : S) :
    finiteBranchPolynomial P t =
      (X * P) ^ 2 - 4 * C t * X := by
  unfold finiteBranchPolynomial
  simp only [map_ofNat, map_mul]
  ring

/-- The two linear coordinates in the actual finite chart. -/
def finiteFamilyNodeMinus (P : S[X]) (t : S) :
    QuadraticAlgebra S[X] (finiteBranchPolynomial P t) 0 :=
  QuadraticAlgebra.omega - algebraMap S[X] _ (X * P)

def finiteFamilyNodePlus (P : S[X]) (t : S) :
    QuadraticAlgebra S[X] (finiteBranchPolynomial P t) 0 :=
  QuadraticAlgebra.omega + algebraMap S[X] _ (X * P)

/-- On the actual finite chart the two coordinates have product `-4TX`. -/
theorem finiteFamilyNodeMinus_mul_plus (P : S[X]) (t : S) :
    finiteFamilyNodeMinus P t * finiteFamilyNodePlus P t =
      algebraMap S[X] _ (-(4 * C t * X)) := by
  have hω :
      (QuadraticAlgebra.omega : QuadraticAlgebra S[X] (finiteBranchPolynomial P t) 0) ^ 2 =
        algebraMap S[X] _ (finiteBranchPolynomial P t) := by
    calc
      _ = (QuadraticAlgebra.omega :
          QuadraticAlgebra S[X] (finiteBranchPolynomial P t) 0) *
          QuadraticAlgebra.omega := by ring
      _ = _ := by simp only [QuadraticAlgebra.omega_mul_omega_eq_algebraMap,
        map_zero, zero_mul, add_zero]
  calc
    _ = (QuadraticAlgebra.omega :
        QuadraticAlgebra S[X] (finiteBranchPolynomial P t) 0) ^ 2 -
        (algebraMap S[X] _ (X * P)) ^ 2 := by
          simp only [finiteFamilyNodeMinus, finiteFamilyNodePlus]
          ring
    _ = _ := by
      rw [hω, ← map_pow, ← map_sub, finiteBranchPolynomial_eq_nodeEquation]
      congr 1; ring

/-- Translation of the square-root generator on the actual finite chart.
The target equation is `Y (Y - 2XP) = -4TX`; the equivalence is over the
polynomial coordinate ring and hence induces an isomorphism of that chart. -/
def finiteFamilyNodeTranslatedEquiv (P : S[X]) (t : S) :
    QuadraticAlgebra S[X] (finiteBranchPolynomial P t) 0 ≃ₐ[S[X]]
      QuadraticAlgebra S[X] (-(4 * C t * X)) (2 * (X * P)) := by
  rw [finiteBranchPolynomial_eq_nodeEquation]
  exact familyNodeTranslatedEquiv (X * P) (C t) X

/-- The translated affine chart is the same finite chart of the scaled
projective cover, expressed in node coordinates. -/
def finiteFamilyNodeTranslatedSpecIso (P : S[X]) (t : S) :
    Spec (CommRingCat.of
      (QuadraticAlgebra S[X] (-(4 * C t * X)) (2 * (X * P)))) ≅
    Spec (CommRingCat.of
      (QuadraticAlgebra S[X] (finiteBranchPolynomial P t) 0)) :=
  Scheme.Spec.mapIso
    (finiteFamilyNodeTranslatedEquiv P t).toRingEquiv.toCommRingCatIso.op

/-- The zero-node chart change is over the same actual finite-chart algebra.
The coefficient `P` becomes a unit on a neighborhood of `u = 0`. -/
def finiteFamilyZeroNodeCoordinateHom (P : S[X]) (t : S) :
    familyZeroNodeAlgebra P X (C t) →ₐ[S[X]]
      QuadraticAlgebra S[X] (finiteBranchPolynomial P t) 0 := by
  rw [finiteBranchPolynomial_eq_nodeEquation]
  exact familyZeroNodeCoordinateHom P X (C t)

/-- The zero-node coordinate product is `-4T²` in the actual chart. -/
theorem finiteFamilyZeroNode_product (P : S[X]) (t : S) :
    familyZeroNodeMinus P X (C t) * familyZeroNodePlus P X (C t) =
      algebraMap S[X]
        (QuadraticAlgebra S[X] ((X * P) ^ 2 - 4 * C t * X) 0)
        (-(4 * (C t) ^ 2)) :=
  familyZeroNodeMinus_mul_familyZeroNodePlus P X (C t)

end HilbertModularity.Hyperelliptic
