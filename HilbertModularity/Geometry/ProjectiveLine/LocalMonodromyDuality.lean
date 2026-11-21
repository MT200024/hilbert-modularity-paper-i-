/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.ProjectiveLine.LocalMonodromyRigidity
public import HilbertModularity.Geometry.Etale.LocalSystem.Duality
public import HilbertModularity.RepresentationTheory.RankTwoDuality
public import HilbertModularity.RepresentationTheory.DualIrreducibility

/-! # Cohomological duality preserves the standard cusp classes

The alternating pairing transports each local basis separately. Only the
three cusp operators need determinant one; no arithmetic determinant identity
is assumed. This proves the duality step in [TripathiGoswami, RMgeneral].
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry
open HilbertModularity.Cyclotomic

namespace AlgebraicGeometry.ProjectiveLine

/-- A rank-two local system and its cohomological dual have the same prescribed
special-linear cusp classes, with the same coefficient and inertia labels. -/
theorem HasStandardLocalMonodromy.cohDual
    {N : ℕ} [NeZero N] {L : Type} [NontriviallyNormedField L]
    [CompleteSpace L] [Algebra ℚ L]
    {σ : realCyclotomicField N →ₐ[ℚ] L}
    {F : Scheme.EtaleLocalSystem (RatFunc (realCyclotomicField N))
      (punctured (realCyclotomicField N)) L}
    {γ : Fin 3 → AlgebraicClosure (RatFunc (realCyclotomicField N)) ≃ₐ[
      RatFunc (realCyclotomicField N)] AlgebraicClosure (RatFunc (realCyclotomicField N))}
    (h : HasStandardLocalMonodromy N L σ F γ) :
    HasStandardLocalMonodromy N L σ F.cohDual γ := by
  intro i
  obtain ⟨b, hb⟩ := h i
  refine ⟨b.map (HilbertModularity.rankTwoAlternatingEquiv b), ?_⟩
  change LinearMap.toMatrix (b.map (HilbertModularity.rankTwoAlternatingEquiv b))
    (b.map (HilbertModularity.rankTwoAlternatingEquiv b))
    (Scheme.fiberMonodromy (RatFunc (realCyclotomicField N))
      (punctured (realCyclotomicField N)) (ModuleCat.cohDual L F.algebraicFunctor)
      (puncturedRationalPoint (realCyclotomicField N))
      (Scheme.galoisToEtaleFundamentalGroup (RatFunc (realCyclotomicField N))
        (puncturedRationalPoint (realCyclotomicField N)) (γ i))) = _
  rw [Scheme.fiberMonodromy_cohDual]
  have hd := HilbertModularity.toMatrix_dual_rankTwoAlternatingEquiv b
    (Scheme.fiberMonodromy (RatFunc (realCyclotomicField N))
      (punctured (realCyclotomicField N)) F.algebraicFunctor
      (puncturedRationalPoint (realCyclotomicField N)))
    (Scheme.galoisToEtaleFundamentalGroup (RatFunc (realCyclotomicField N))
      (puncturedRationalPoint (realCyclotomicField N)) (γ i))
    ((congrArg Matrix.det hb).trans
      (HilbertModularity.Monodromy.standardTriple (σ (tau N 1)) i).property)
  exact hd.trans hb

/-- Rigidity identifies a geometrically irreducible standard local system with
its cohomological dual on the geometric kernel. The arithmetic actions need not
be equivalent. This is a deduction from [YunRigid2014, Proposition 3.2.7 and Theorem 3.2.8]. -/
theorem geometricEquiv_cohDual_of_standard_localMonodromy_charZero
    (N : ℕ) [NeZero N] (hN : 3 ≤ N) (p : ℕ) [Fact p.Prime]
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
    [Algebra ℚ L] [IsScalarTower ℚ ℚ_[p] L]
    (σ : realCyclotomicField N →ₐ[ℚ] L)
    (F : Scheme.EtaleLocalSystem (RatFunc (realCyclotomicField N))
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
    (hF : HasStandardLocalMonodromy N L σ F γ) :
    let x := puncturedRationalPoint (realCyclotomicField N)
    let ρ := Scheme.fiberMonodromy (RatFunc (realCyclotomicField N))
      (punctured (realCyclotomicField N)) F.algebraicFunctor x
    let ρdual := Scheme.fiberMonodromy (RatFunc (realCyclotomicField N))
      (punctured (realCyclotomicField N)) F.cohDual.algebraicFunctor x
    let k := (Scheme.etaleFundamentalGroupMap (puncturedToSpec (realCyclotomicField N))
      (RatFunc (realCyclotomicField N)) x).ker.subtype
    Representation.IsIrreducible (ρ.comp k) →
      Nonempty (Representation.Equiv (ρ.comp k) (ρdual.comp k)) := by
  intro x ρ ρdual k hirred
  have : Module.Finite L (F.algebraicFunctor.obj
      (Scheme.etaleFiberPoint (RatFunc (realCyclotomicField N))
        (punctured (realCyclotomicField N)) x)) := F.finite _
  have : Representation.IsIrreducible (ρ.comp k) := hirred
  have hdual : Representation.IsIrreducible (ρdual.comp k) := by
    have he := Scheme.fiberMonodromy_cohDual (RatFunc (realCyclotomicField N))
      (punctured (realCyclotomicField N)) F.algebraicFunctor x
    change Representation.IsIrreducible
      ((Scheme.fiberMonodromy (RatFunc (realCyclotomicField N))
        (punctured (realCyclotomicField N)) (ModuleCat.cohDual L F.algebraicFunctor) x).comp k)
    have heq := (congrArg (fun r => r.comp k) he).trans
      (Representation.dual_compHom ρ k)
    exact (congrArg Representation.IsIrreducible heq).mpr
      (Representation.isIrreducible_dual (ρ.comp k))
  exact geometricEquiv_of_standard_localMonodromy_charZero N L σ hN p
    F F.cohDual γ c ζ hinertia horientation hlabel hF hF.cohDual hirred hdual


/-- Compatibility with the earlier odd-coefficient API. -/
theorem geometricEquiv_cohDual_of_standard_localMonodromy
    (N : ℕ) [NeZero N] (hN : 3 ≤ N) (p : ℕ) [Fact p.Prime] (_hp : p ≠ 2)
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
    [Algebra ℚ L] [IsScalarTower ℚ ℚ_[p] L]
    (σ : realCyclotomicField N →ₐ[ℚ] L)
    (F : Scheme.EtaleLocalSystem (RatFunc (realCyclotomicField N))
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
    (hF : HasStandardLocalMonodromy N L σ F γ) :
    let x := puncturedRationalPoint (realCyclotomicField N)
    let ρ := Scheme.fiberMonodromy (RatFunc (realCyclotomicField N))
      (punctured (realCyclotomicField N)) F.algebraicFunctor x
    let ρdual := Scheme.fiberMonodromy (RatFunc (realCyclotomicField N))
      (punctured (realCyclotomicField N)) F.cohDual.algebraicFunctor x
    let k := (Scheme.etaleFundamentalGroupMap (puncturedToSpec (realCyclotomicField N))
      (RatFunc (realCyclotomicField N)) x).ker.subtype
    Representation.IsIrreducible (ρ.comp k) →
      Nonempty (Representation.Equiv (ρ.comp k) (ρdual.comp k)) := by
  exact geometricEquiv_cohDual_of_standard_localMonodromy_charZero N hN p L σ F γ c ζ hinertia horientation hlabel hF

end AlgebraicGeometry.ProjectiveLine
