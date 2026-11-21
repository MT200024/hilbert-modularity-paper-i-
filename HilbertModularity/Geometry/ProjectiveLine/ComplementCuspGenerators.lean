/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.ProjectiveLine.NormalizedCuspGenerators
public import HilbertModularity.Geometry.ProjectiveLine.GenericFiberPath
public import HilbertModularity.Geometry.Etale.ParameterInvolution
public import HilbertModularity.NumberTheory.Cyclotomic

/-! # Oriented cusp generators at the fixed midpoint

The external input is the functorial presentation of the geometric fundamental
group of the three-punctured line. It contains no representation, local-system
comparison, or arithmetic character. Its orientation is the same one used by
the prescribed hypergeometric inertia classes.
-/

public noncomputable section

open CategoryTheory
open HilbertModularity.Cyclotomic

namespace AlgebraicGeometry.ProjectiveLine

/-- Oriented inertia lifts and their actual midpoint loops, with the
functorial complement action. This data object contains no representation. -/
structure ComplementCuspGenerators (N : ℕ) [NeZero N] where
  gamma : Fin 3 → AlgebraicClosure (RatFunc (realCyclotomicField N)) ≃ₐ[
    RatFunc (realCyclotomicField N)] AlgebraicClosure (RatFunc (realCyclotomicField N))
  conjugator : Fin 3 → AlgebraicClosure (RatFunc (realCyclotomicField N)) ≃ₐ[
    RatFunc (realCyclotomicField N)] AlgebraicClosure (RatFunc (realCyclotomicField N))
  roots : ℕ → AlgebraicClosure (RatFunc (realCyclotomicField N))
  inertia : ∀ i, (Subgroup.zpowers (gamma i)).topologicalClosure =
    (![RatFunc.affineInertia (realCyclotomicField N) 0,
      RatFunc.affineInertia (realCyclotomicField N) 1,
      RatFunc.infinityInertia (realCyclotomicField N)] i).map
        (MulAut.conj (conjugator i)).toMonoidHom
  orientation : HasCommonCuspOrientation (realCyclotomicField N) gamma roots
  label : roots N + (roots N)⁻¹ = algebraMap (realCyclotomicField N) _ (tau N 1)
  loops : Fin 3 → (Scheme.etaleFundamentalGroupMap
    (puncturedToSpec (realCyclotomicField N)) (realCyclotomicField N)
    (puncturedPoint (realCyclotomicField N) (midpointParameter (realCyclotomicField N)))).ker
  path_loops : ∀ i, Scheme.geometricFiberPathGroupEquiv _ _
    (puncturedGenericFiberPath (realCyclotomicField N)
      (puncturedPoint (realCyclotomicField N) (midpointParameter (realCyclotomicField N))))
    (Scheme.galoisToEtaleFundamentalGroup (RatFunc (realCyclotomicField N))
      (puncturedRationalPoint (realCyclotomicField N)) (gamma i)) = loops i
  product : loops 0 * loops 1 * loops 2 = 1
  dense : Dense (Subgroup.closure ({loops 0, loops 1} : Set
    (Scheme.etaleFundamentalGroupMap
      (puncturedToSpec (realCyclotomicField N)) (realCyclotomicField N)
      (puncturedPoint (realCyclotomicField N) (midpointParameter (realCyclotomicField N)))).ker) :
    Set (Scheme.etaleFundamentalGroupMap
      (puncturedToSpec (realCyclotomicField N)) (realCyclotomicField N)
      (puncturedPoint (realCyclotomicField N) (midpointParameter (realCyclotomicField N)))).ker)
  complement : (Scheme.etaleFundamentalGroupMap
    (puncturedToSpec (realCyclotomicField N)) (realCyclotomicField N)
    (puncturedPoint (realCyclotomicField N) (midpointParameter (realCyclotomicField N)))).ker ≃ₜ*
      (Scheme.etaleFundamentalGroupMap
        (puncturedToSpec (realCyclotomicField N)) (realCyclotomicField N)
        (puncturedPoint (realCyclotomicField N) (midpointParameter (realCyclotomicField N)))).ker
  complement_coe : ∀ g, (complement g : Scheme.etaleFundamentalGroup (realCyclotomicField N)
    (puncturedPoint (realCyclotomicField N) (midpointParameter (realCyclotomicField N)))) =
      complementFundamentalAutomorphism (realCyclotomicField N) g
  complement_zero : complement (loops 0) = loops 1
  complement_one : complement (loops 1) = loops 0

/-- **Named literature input.** The characteristic-zero Riemann existence
comparison and its functoriality [src_milne_lec, Remark 3.3(a)--(c), p.27;
Theorem 3.4, p.28], together with the arithmetic exact sequence and punctured
sphere presentation [src_milne_lec, pp.29--30], give these actual geometric
generators. See also [GPRV, Theorem 3.15, p.11]. The normalization by compatible
roots and conjugates of local inertia is [DarmonFibres, section 1, p.2];
section 2, p.3 records the product-one choice.

Over the complex numbers, take a positively oriented loop around zero with
a straight stem from `1/2`, and its image under the holomorphic map `1-z`.
These loops are exchanged exactly and generate the twice-punctured plane
group. Their product inverse is the infinity loop. Riemann existence transfers
this description, with its scheme-induced automorphism, to the actual
geometric kernel. Changing to the specified generic fibre path conjugates
the inertia lifts. Choose the common root system with the specified primitive
`N`-th root sum; no coefficient embedding of a representation is chosen here.
These standard topological and inertia-transport consequences are included in
this one literature input, rather than asserted as a verbatim source theorem.

In particular this input does not assert invariance of any chosen Euler or
Darmon local system. The invariance of its monodromy matrices remains a
separate manuscript deduction. -/
theorem exists_complementCuspGenerators (N : ℕ) [NeZero N] (hN : 3 ≤ N) :
    Nonempty (ComplementCuspGenerators N) := by
  sorry

end AlgebraicGeometry.ProjectiveLine
