/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RingTheory.AdjoinRoot.Etale
public import HilbertModularity.RingTheory.AdjoinRoot.RootsOfUnity
public import HilbertModularity.Geometry.Etale.Affine
public import HilbertModularity.Geometry.ProjectiveLine.CoordinateRing

/-! # The affine Euler cover

We construct the actual root algebra for
`y^N = x^m (1-x)^(N-m) (1-t*x)^m` on the complement of the finite branch
sections. This is the affine part of the Euler realization specified in
[TripathiGoswamiRevised]. The parameter `m` occurs in these exponents;
the associated primitive deck character is not raised to `m` a second time.
-/

@[expose] public noncomputable section

open CategoryTheory Polynomial AlgebraicGeometry

namespace HilbertModularity.Hypergeometric.EulerCover

universe u
variable {R : Type u} [CommRing R]

/-- The product whose nonvanishing defines the complement of the finite branch sections. -/
def branchProduct (t : R) : R[X] := X * (1 - X) * (1 - C t * X)

/-- The polynomial on the right-hand side of the specified Euler equation. -/
def branchPolynomial (N m : ℕ) (t : R) : R[X] :=
  X ^ m * (1 - X) ^ (N - m) * (1 - C t * X) ^ m

/-- Coordinates on the affine branch complement. -/
abbrev BaseRing (t : R) := Localization.Away (branchProduct t)

/-- The actual radicand on the branch complement. -/
def radicand (N m : ℕ) (t : R) : BaseRing t :=
  algebraMap R[X] (BaseRing t) (branchPolynomial N m t)

/-- The defining monic equation in the covering coordinate. -/
def coverPolynomial (N m : ℕ) (t : R) : (BaseRing t)[X] :=
  X ^ N - C (radicand N m t)

/-- The actual Euler-cover algebra on the branch complement. -/
abbrev CoverRing (N m : ℕ) (t : R) := AdjoinRoot (coverPolynomial N m t)

/-- The covering coordinate in the actual root algebra. -/
def coverRoot (N m : ℕ) (t : R) : CoverRing N m t :=
  AdjoinRoot.root (coverPolynomial N m t)

/-- The covering coordinate satisfies the original Euler equation exactly. -/
theorem coverRoot_pow (N m : ℕ) (t : R) :
    coverRoot N m t ^ N = algebraMap (BaseRing t) (CoverRing N m t) (radicand N m t) :=
  AdjoinRoot.root_X_pow_sub_C_pow N (radicand N m t)

/-- The radicand is a unit on the branch complement, without changing its sign. -/
theorem isUnit_radicand (N m : ℕ) (t : R) : IsUnit (radicand N m t) := by
  have h : IsUnit (algebraMap R[X] (BaseRing t) (branchProduct t)) :=
    IsLocalization.Away.algebraMap_isUnit (branchProduct t)
  simp only [branchProduct, map_mul, IsUnit.mul_iff] at h
  have hu := ((h.1.1.pow m).mul (h.1.2.pow (N - m))).mul (h.2.pow m)
  simpa only [radicand, branchPolynomial, map_mul, map_pow] using hu

/-- The defining polynomial is monic for a nonzero covering degree. -/
theorem coverPolynomial_monic (N m : ℕ) (t : R) (hN : N ≠ 0) :
    (coverPolynomial N m t).Monic := monic_X_pow_sub_C _ hN

/-- The actual cover algebra is finite over its branch-complement coordinates. -/
theorem coverRing_finite (N m : ℕ) (t : R) (hN : N ≠ 0) :
    Module.Finite (BaseRing t) (CoverRing N m t) :=
  (coverPolynomial_monic N m t hN).finite_adjoinRoot

/-- The actual cover algebra is free over its branch-complement coordinates. -/
theorem coverRing_free (N m : ℕ) (t : R) (hN : N ≠ 0) :
    Module.Free (BaseRing t) (CoverRing N m t) :=
  (coverPolynomial_monic N m t hN).free_adjoinRoot

/-- Inverting the covering degree makes the actual branch-open Euler algebra étale. -/
theorem coverRing_etale (N m : ℕ) (t : R) (hN : N ≠ 0) (hn : IsUnit (N : R)) :
    Algebra.Etale (BaseRing t) (CoverRing N m t) := by
  apply AdjoinRoot.etale_of_monic_of_separable (coverPolynomial_monic N m t hN)
  obtain ⟨a, ha⟩ := isUnit_radicand N m t
  have hn' : IsUnit (N : BaseRing t) := by
    simpa using (hn.map (Polynomial.C : R →+* R[X])).map (algebraMap R[X] (BaseRing t))
  simpa only [coverPolynomial, ha] using Polynomial.separable_X_pow_sub_C_unit (n := N) a hn'

/-- The affine scheme of the actual Euler-cover algebra. -/
def affineScheme (N m : ℕ) (t : R) : Scheme := Spec (CommRingCat.of (CoverRing N m t))

/-- The structural morphism keeps the original parameter coefficient ring fixed. -/
def structureMap (N m : ℕ) (t : R) : affineScheme N m t ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom ((algebraMap (BaseRing t) (CoverRing N m t)).comp
    ((algebraMap R[X] (BaseRing t)).comp Polynomial.C)))

/-- The constructed root algebra as an object of the established finite étale algebra category. -/
def finiteEtaleAlgebra (N m : ℕ) (t : R) (hN : N ≠ 0) (hn : IsUnit (N : R)) :
    CommAlgCat.FiniteEtale (BaseRing t) := by
  have := coverRing_finite N m t hN
  have := coverRing_etale N m t hN hn
  exact CommAlgCat.FiniteEtale.of (BaseRing t) (CoverRing N m t)

/-- The actual finite étale Euler cover of the affine branch complement. -/
def finiteEtaleCover (N m : ℕ) (t : R) (hN : N ≠ 0) (hn : IsUnit (N : R)) :
    (Spec (CommRingCat.of (BaseRing t))).FiniteEtale :=
  Scheme.finiteEtaleAlgebraCover (BaseRing t) (finiteEtaleAlgebra N m t hN hn)

/-- The bundled finite étale cover has exactly the displayed affine Euler scheme as its source. -/
theorem finiteEtaleCover_left (N m : ℕ) (t : R) (hN : N ≠ 0) (hn : IsUnit (N : R)) :
    (finiteEtaleCover N m t hN hn).obj.left = affineScheme N m t := rfl

/-- The finite étale covering map is the actual spectrum map of the root-algebra inclusion. -/
theorem finiteEtaleCover_hom (N m : ℕ) (t : R) (hN : N ≠ 0) (hn : IsUnit (N : R)) :
    (finiteEtaleCover N m t hN hn).obj.hom =
      Spec.map (CommRingCat.ofHom (algebraMap (BaseRing t) (CoverRing N m t))) := rfl

variable (R)

/-- The affine Euler family over the existing punctured-parameter coordinate ring. -/
def affineFamily (N m : ℕ) : Scheme :=
  affineScheme N m
    (algebraMap R[X] (ProjectiveLine.puncturedCoordinateRing R) X)

/-- The actual family morphism to the projective parameter line minus zero, one and infinity. -/
def familyStructureMap (N m : ℕ) : affineFamily R N m ⟶ ProjectiveLine.punctured R :=
  structureMap N m
      (algebraMap R[X] (ProjectiveLine.puncturedCoordinateRing R) X) ≫
    (ProjectiveLine.puncturedAffineIso R).inv

end HilbertModularity.Hypergeometric.EulerCover
