/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.GenericCuspComplement
public import HilbertModularity.Geometry.ProjectiveLine.ComplementCuspGenerators
public import HilbertModularity.Geometry.ProjectiveLine.LocalMonodromyRigidity

/-! # Applying oriented cusp geometry to hypergeometric local classes -/

public noncomputable section

open AlgebraicGeometry
open HilbertModularity.Cyclotomic

namespace HilbertModularity.Hypergeometric

/-- Specialize generic-point transport once to the actual rational-function
field and its specified midpoint path. The remaining arguments are the
oriented cusp generators and their local classes. -/
private theorem cyclotomicGenericCuspComparison
    (N : ℕ) [NeZero N]
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    (τ : L) (hτ : τ ≠ 2)
    (F : Scheme.EtaleLocalSystem (realCyclotomicField N)
      (ProjectiveLine.punctured (realCyclotomicField N)) L)
    (Fgen : Scheme.EtaleLocalSystem (RatFunc (realCyclotomicField N))
      (ProjectiveLine.punctured (realCyclotomicField N)) L)
    (ePath : Representation.Equiv
      (Scheme.fiberMonodromy (RatFunc (realCyclotomicField N))
        (ProjectiveLine.punctured (realCyclotomicField N)) Fgen.algebraicFunctor
        (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N)))
      ((puncturedFiberMonodromy (realCyclotomicField N)
        (ProjectiveLine.midpointParameter (realCyclotomicField N)) F).comp
          (Scheme.geometricFiberPathGroupEquiv _ _
            (ProjectiveLine.puncturedGenericFiberPath (realCyclotomicField N)
              (ProjectiveLine.puncturedPoint (realCyclotomicField N)
                (ProjectiveLine.midpointParameter (realCyclotomicField N))))).toMonoidHom)) :
    let K : Type := realCyclotomicField N
    let Kgen : Type := RatFunc K
    let xgen := ProjectiveLine.puncturedRationalPoint K
    let pathIso := ProjectiveLine.puncturedGenericFiberPath K
      (ProjectiveLine.puncturedPoint K (ProjectiveLine.midpointParameter K))
    let ξ₀ := ProjectiveLine.midpointParameter K
    let x := ProjectiveLine.puncturedPoint K ξ₀
    let π := Scheme.etaleFundamentalGroupMap (ProjectiveLine.puncturedToSpec K) K x
    let path := Scheme.geometricFiberPathGroupEquiv Kgen K
      pathIso
    ∀ (g : Fin 3 → Scheme.etaleFundamentalGroup Kgen
        xgen)
      (a b d : π.ker),
        path (g 0) = (a : Scheme.etaleFundamentalGroup K x) →
        path (g 1) = (b : Scheme.etaleFundamentalGroup K x) →
        path (g 2) = (d : Scheme.etaleFundamentalGroup K x) →
        a * b * d = 1 → Dense (Subgroup.closure ({a, b} : Set π.ker) : Set π.ker) →
        (∀ i, ∃ B : Module.Basis (Fin 2) L (Fgen.toFunctor.obj
          (Scheme.etaleFiberPoint Kgen (ProjectiveLine.punctured K)
            xgen)),
          LinearMap.toMatrix B B (Scheme.fiberMonodromy Kgen
            (ProjectiveLine.punctured K) Fgen.algebraicFunctor
            xgen (g i)) =
              (Monodromy.standardTriple τ i : Matrix (Fin 2) (Fin 2) L)) →
        ∀ (α : π.ker ≃ₜ* π.ker),
          (∀ g : π.ker, (α g : Scheme.etaleFundamentalGroup K x) =
            ProjectiveLine.complementFundamentalAutomorphism K g) → α a = b → α b = a →
      let k := (puncturedArithmeticProjectionHom K ξ₀).ker.subtype
      Nonempty (Representation.Equiv ((puncturedFiberMonodromy K ξ₀ F).comp k)
        ((puncturedFiberMonodromy K ξ₀ (F.complementPullback K L)).comp k)) ∧
        (Representation.baseChange (AlgebraicClosure L)
          ((puncturedFiberMonodromy K ξ₀ F).comp k)).IsIrreducible :=
  geometricComplementEquiv_of_genericCuspClasses
    (realCyclotomicField N) (RatFunc (realCyclotomicField N)) L
    (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N))
    (ProjectiveLine.puncturedGenericFiberPath (realCyclotomicField N)
      (ProjectiveLine.puncturedPoint (realCyclotomicField N)
        (ProjectiveLine.midpointParameter (realCyclotomicField N))))
    τ hτ F Fgen ePath

/-- Prescribed oriented hypergeometric local classes imply geometric
invariance of the actual complement pullback. The generic and rational
fibres are related by the specified actual fibre path. -/
theorem geometricComplementEquiv_of_standardLocalMonodromy
    (N : ℕ) [NeZero N] (C : ProjectiveLine.ComplementCuspGenerators N)
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L] [Algebra ℚ L]
    (σ : realCyclotomicField N →ₐ[ℚ] L) (hτ : σ (tau N 1) ≠ 2)
    (F : Scheme.EtaleLocalSystem (realCyclotomicField N)
      (ProjectiveLine.punctured (realCyclotomicField N)) L)
    (Fgen : Scheme.EtaleLocalSystem (RatFunc (realCyclotomicField N))
      (ProjectiveLine.punctured (realCyclotomicField N)) L)
    (ePath : Representation.Equiv
      (Scheme.fiberMonodromy (RatFunc (realCyclotomicField N))
        (ProjectiveLine.punctured (realCyclotomicField N)) Fgen.algebraicFunctor
        (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N)))
      ((puncturedFiberMonodromy (realCyclotomicField N)
        (ProjectiveLine.midpointParameter (realCyclotomicField N)) F).comp
          (Scheme.geometricFiberPathGroupEquiv _ _
            (ProjectiveLine.puncturedGenericFiberPath (realCyclotomicField N)
              (ProjectiveLine.puncturedPoint (realCyclotomicField N)
                (ProjectiveLine.midpointParameter (realCyclotomicField N))))).toMonoidHom))
    (hclasses : ProjectiveLine.HasStandardLocalMonodromy N L σ Fgen C.gamma) :
    let K : Type := realCyclotomicField N
    let ξ₀ := ProjectiveLine.midpointParameter K
    let k := (puncturedArithmeticProjectionHom K ξ₀).ker.subtype
    Nonempty (Representation.Equiv ((puncturedFiberMonodromy K ξ₀ F).comp k)
      ((puncturedFiberMonodromy K ξ₀ (F.complementPullback K L)).comp k)) ∧
      (Representation.baseChange (AlgebraicClosure L)
        ((puncturedFiberMonodromy K ξ₀ F).comp k)).IsIrreducible := by
  let K : Type := realCyclotomicField N
  exact cyclotomicGenericCuspComparison N L (σ (tau N 1)) hτ F Fgen ePath
      (fun i => Scheme.galoisToEtaleFundamentalGroup (RatFunc K)
        (ProjectiveLine.puncturedRationalPoint K) (C.gamma i))
        (C.loops 0) (C.loops 1) (C.loops 2)
        (C.path_loops 0) (C.path_loops 1) (C.path_loops 2) C.product C.dense
        (fun i => ProjectiveLine.HasStandardLocalMonodromy.at N L σ hclasses i)
        C.complement C.complement_coe C.complement_zero C.complement_one

end HilbertModularity.Hypergeometric
