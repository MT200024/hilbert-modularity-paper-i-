/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.ProjectiveLine.NormalizedCuspGenerators
public import HilbertModularity.Geometry.ProjectiveLine.RationalCoordinate
public import HilbertModularity.Geometry.Etale.LocalSystem
public import HilbertModularity.Geometry.Etale.Pullback
public import HilbertModularity.NumberTheory.Cyclotomic
public import HilbertModularity.Monodromy.Admissible
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Analysis.Normed.Module.Basic

/-! # Geometric rigidity with the prescribed coefficient label

The standard rank-two triple is cohomologically rigid on the three-punctured
projective line. The geometric uniqueness input uses [YunRigid2014,
Proposition 3.2.7 and Theorem 3.2.8], the latter stating Katz's Theorem 5.0.2.
It applies to every finite `p`-adic coefficient extension, including `p = 2`.
The older odd-coefficient API remains a proved specialization, consistent
with the standing restriction in [DarmonFibres, §1, Proposition 2.4].
The actual local classes, their orientation and coefficient label are fixed.
No arithmetic comparison character or manuscript-family comparison is assumed.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry
open HilbertModularity.Cyclotomic

namespace AlgebraicGeometry.ProjectiveLine

variable (N : ℕ) [NeZero N]
  (L : Type) [NontriviallyNormedField L] [Algebra ℚ L]
  (σ : realCyclotomicField N →ₐ[ℚ] L)

/-- Each cusp has the prescribed conjugacy class. Its basis may depend on the
cusp; this is deliberately weaker than simultaneous equality of triples. -/
@[expose] def HasStandardLocalMonodromy
    (F : Scheme.EtaleLocalSystem (RatFunc (realCyclotomicField N))
      (punctured (realCyclotomicField N)) L)
    (γ : Fin 3 → AlgebraicClosure (RatFunc (realCyclotomicField N)) ≃ₐ[
      RatFunc (realCyclotomicField N)] AlgebraicClosure (RatFunc (realCyclotomicField N))) : Prop :=
  ∀ i, ∃ b : Module.Basis (Fin 2) L
      (F.toFunctor.obj (Scheme.etaleFiberPoint (RatFunc (realCyclotomicField N))
        (punctured (realCyclotomicField N)) (puncturedRationalPoint (realCyclotomicField N)))),
    LinearMap.toMatrix b b
      (Scheme.fiberMonodromy (RatFunc (realCyclotomicField N))
        (punctured (realCyclotomicField N)) F.algebraicFunctor
        (puncturedRationalPoint (realCyclotomicField N))
        (Scheme.galoisToEtaleFundamentalGroup (RatFunc (realCyclotomicField N))
          (puncturedRationalPoint (realCyclotomicField N)) (γ i))) =
      (HilbertModularity.Monodromy.standardTriple (σ (tau N 1)) i :
        Matrix (Fin 2) (Fin 2) L)

/-- Read one oriented local class without unfolding the completed
`RatFunc` coefficient instances in downstream geometric arguments. -/
theorem HasStandardLocalMonodromy.at
    {F : Scheme.EtaleLocalSystem (RatFunc (realCyclotomicField N))
      (punctured (realCyclotomicField N)) L}
    {γ : Fin 3 → AlgebraicClosure (RatFunc (realCyclotomicField N)) ≃ₐ[
      RatFunc (realCyclotomicField N)] AlgebraicClosure (RatFunc (realCyclotomicField N))}
    (h : HasStandardLocalMonodromy N L σ F γ) (i : Fin 3) :
    ∃ b : Module.Basis (Fin 2) L
      (F.toFunctor.obj (Scheme.etaleFiberPoint (RatFunc (realCyclotomicField N))
        (punctured (realCyclotomicField N)) (puncturedRationalPoint (realCyclotomicField N)))),
      LinearMap.toMatrix b b
        (Scheme.fiberMonodromy (RatFunc (realCyclotomicField N))
          (punctured (realCyclotomicField N)) F.algebraicFunctor
          (puncturedRationalPoint (realCyclotomicField N))
          (Scheme.galoisToEtaleFundamentalGroup (RatFunc (realCyclotomicField N))
            (puncturedRationalPoint (realCyclotomicField N)) (γ i))) =
        (HilbertModularity.Monodromy.standardTriple (σ (tau N 1)) i :
          Matrix (Fin 2) (Fin 2) L) :=
  h i

/-- **Named literature input.** [YunRigid2014, §3.1.1, p.33; §3.2,
p.35; Proposition 3.2.7 and Theorem 3.2.8, p.39] gives the local-system
dictionary, numerical cohomological rigidity criterion and physical rigidity
on `P¹`. The last theorem explicitly cites [KatzRigid1996, Theorem 5.0.2];
that attribution is through the inspected Yun text, not an independently
inspected quotation from Katz.

Here the geometric base has characteristic zero. Each of the three standard
local matrices is non-scalar and has a one-dimensional centralizer in the
trace-free endomorphisms; the Swan conductors vanish. Irreducibility is absolute:
a nontrivial unipotent has its unique invariant line defined over `L`.
Consequently the global trace-free invariants vanish, and the sum of the three
Artin conductors is `6 = 2 * dim(sl₂)`. Yun's criterion gives cohomological
rigidity, hence geometric uniqueness over an algebraic closure of `L`.
The space of intertwiners is the kernel of linear equations over `L`; scalar
extension preserves that kernel, and a nonzero intertwiner between these
irreducible rank-two actions is invertible. This descends the equivalence to
`L`. These standard specialization and coefficient-descent consequences are
included in this single admission. No source is claimed to state the entire
Lean signature verbatim. In particular, no restriction on the coefficient
prime is inferred from a restriction on the characteristic of the geometric
base, and no freeness of the local monodromy action is asserted. -/
theorem geometricEquiv_of_standard_localMonodromy_charZero
    (hN : 3 ≤ N) (p : ℕ) [Fact p.Prime]
    [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
    [IsScalarTower ℚ ℚ_[p] L]
    (F F' : Scheme.EtaleLocalSystem (RatFunc (realCyclotomicField N))
      (punctured (realCyclotomicField N)) L)
    (γ c : Fin 3 → AlgebraicClosure (RatFunc (realCyclotomicField N)) ≃ₐ[
      RatFunc (realCyclotomicField N)] AlgebraicClosure (RatFunc (realCyclotomicField N)))
    (ζ : ℕ → AlgebraicClosure (RatFunc (realCyclotomicField N)))
    (hinertia : ∀ i, (Subgroup.zpowers (γ i)).topologicalClosure =
      (![RatFunc.affineInertia (realCyclotomicField N) 0,
         RatFunc.affineInertia (realCyclotomicField N) 1,
         RatFunc.infinityInertia (realCyclotomicField N)] i).map (MulAut.conj (c i)).toMonoidHom)
    (horientation : HasCommonCuspOrientation (realCyclotomicField N) γ ζ)
    (hlabel : ζ N + (ζ N)⁻¹ = algebraMap (realCyclotomicField N) _ (tau N 1))
    (hF : HasStandardLocalMonodromy N L σ F γ)
    (hF' : HasStandardLocalMonodromy N L σ F' γ) :
    let x := puncturedRationalPoint (realCyclotomicField N)
    let ρ := Scheme.fiberMonodromy (RatFunc (realCyclotomicField N))
      (punctured (realCyclotomicField N)) F.algebraicFunctor x
    let ρ' := Scheme.fiberMonodromy (RatFunc (realCyclotomicField N))
      (punctured (realCyclotomicField N)) F'.algebraicFunctor x
    let k := (Scheme.etaleFundamentalGroupMap (puncturedToSpec (realCyclotomicField N))
      (RatFunc (realCyclotomicField N)) x).ker.subtype
    Representation.IsIrreducible (ρ.comp k) → Representation.IsIrreducible (ρ'.comp k) →
      Nonempty (Representation.Equiv (ρ.comp k) (ρ'.comp k)) := by
  sorry


/-- The previous odd-coefficient interface is a specialization of the
characteristic-zero geometric rigidity input; its source is not discharged. -/
theorem geometricEquiv_of_standard_localMonodromy
    (hN : 3 ≤ N) (p : ℕ) [Fact p.Prime] (_hp : p ≠ 2)
    [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
    [IsScalarTower ℚ ℚ_[p] L]
    (F F' : Scheme.EtaleLocalSystem (RatFunc (realCyclotomicField N))
      (punctured (realCyclotomicField N)) L)
    (γ c : Fin 3 → AlgebraicClosure (RatFunc (realCyclotomicField N)) ≃ₐ[
      RatFunc (realCyclotomicField N)] AlgebraicClosure (RatFunc (realCyclotomicField N)))
    (ζ : ℕ → AlgebraicClosure (RatFunc (realCyclotomicField N)))
    (hinertia : ∀ i, (Subgroup.zpowers (γ i)).topologicalClosure =
      (![RatFunc.affineInertia (realCyclotomicField N) 0,
         RatFunc.affineInertia (realCyclotomicField N) 1,
         RatFunc.infinityInertia (realCyclotomicField N)] i).map (MulAut.conj (c i)).toMonoidHom)
    (horientation : HasCommonCuspOrientation (realCyclotomicField N) γ ζ)
    (hlabel : ζ N + (ζ N)⁻¹ = algebraMap (realCyclotomicField N) _ (tau N 1))
    (hF : HasStandardLocalMonodromy N L σ F γ)
    (hF' : HasStandardLocalMonodromy N L σ F' γ) :
    let x := puncturedRationalPoint (realCyclotomicField N)
    let ρ := Scheme.fiberMonodromy (RatFunc (realCyclotomicField N))
      (punctured (realCyclotomicField N)) F.algebraicFunctor x
    let ρ' := Scheme.fiberMonodromy (RatFunc (realCyclotomicField N))
      (punctured (realCyclotomicField N)) F'.algebraicFunctor x
    let k := (Scheme.etaleFundamentalGroupMap (puncturedToSpec (realCyclotomicField N))
      (RatFunc (realCyclotomicField N)) x).ker.subtype
    Representation.IsIrreducible (ρ.comp k) → Representation.IsIrreducible (ρ'.comp k) →
      Nonempty (Representation.Equiv (ρ.comp k) (ρ'.comp k)) := by
  exact geometricEquiv_of_standard_localMonodromy_charZero N L σ hN p
    F F' γ c ζ hinertia horientation hlabel hF hF'

end AlgebraicGeometry.ProjectiveLine
