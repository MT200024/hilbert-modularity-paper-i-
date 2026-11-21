/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.HypergeometricCuspMatrices
public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.CoefficientTopology
public import HilbertModularity.Geometry.ProjectiveLine.LocalMonodromyRigidity
public import HilbertModularity.Geometry.ProjectiveLine.LocalMonodromyDuality

/-! # Applying rigidity to the chosen Darmon family

The coefficient label and the actual chosen family are retained. The other
local system must supply its local conjugacy classes and geometric
irreducibility; the Darmon-side hypotheses are proved from its realization.
This is the local-monodromy application in [TripathiGoswami, proof of
RMgeneral, Step 2], using [DarmonFibres, Proposition 2.4].
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic

/-- A geometrically irreducible local system with the prescribed oriented local
classes is geometrically equivalent to the chosen labelled Darmon Tate family.
Only the other family's local classes and irreducibility are hypotheses. -/
theorem darmonLabelledMonodromy_geometricEquiv_of_localMonodromy_charZero
    (N : ℕ) [NeZero N] (hN : 3 ≤ N) (p : ℕ) [Fact p.Prime]
    (L : Type) [NontriviallyNormedField L] [NormedAlgebra ℚ_[p] L]
    [FiniteDimensional ℚ_[p] L] [Algebra ℚ L] [IsScalarTower ℚ ℚ_[p] L]
    (hL : ∀ a : realCyclotomicField N, ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (σ : realCyclotomicField N →ₐ[ℚ] L)
    (F : Scheme.EtaleLocalSystem (RatFunc (realCyclotomicField N))
      (ProjectiveLine.punctured (realCyclotomicField N)) L)
    (hlocal : ∀
      (γ c : Fin 3 → AlgebraicClosure (RatFunc (realCyclotomicField N)) ≃ₐ[
        RatFunc (realCyclotomicField N)] AlgebraicClosure (RatFunc (realCyclotomicField N)))
      (ζ : ℕ → AlgebraicClosure (RatFunc (realCyclotomicField N))),
      (∀ i, (Subgroup.zpowers (γ i)).topologicalClosure =
        (![RatFunc.affineInertia (realCyclotomicField N) 0,
           RatFunc.affineInertia (realCyclotomicField N) 1,
           RatFunc.infinityInertia (realCyclotomicField N)] i).map
             (MulAut.conj (c i)).toMonoidHom) →
      ProjectiveLine.HasCommonCuspOrientation (realCyclotomicField N) γ ζ →
      ζ N + (ζ N)⁻¹ = algebraMap (realCyclotomicField N) _ (tau N 1) →
      ProjectiveLine.HasStandardLocalMonodromy N L σ F γ) :
    let x := ProjectiveLine.puncturedRationalPoint (realCyclotomicField N)
    let FRM := GroupScheme.labelledTateEtaleLocalSystem (RatFunc (realCyclotomicField N))
      (darmonFamily N hN) p L (realCyclotomicField N)
      (darmonRealMultiplication N hN) hL σ
    let ρRM := Scheme.fiberMonodromy (RatFunc (realCyclotomicField N))
      (ProjectiveLine.punctured (realCyclotomicField N)) FRM.algebraicFunctor x
    let ρ := Scheme.fiberMonodromy (RatFunc (realCyclotomicField N))
      (ProjectiveLine.punctured (realCyclotomicField N)) F.algebraicFunctor x
    let k := (Scheme.etaleFundamentalGroupMap
      (ProjectiveLine.puncturedToSpec (realCyclotomicField N))
      (RatFunc (realCyclotomicField N)) x).ker.subtype
    Representation.IsIrreducible (ρ.comp k) →
      Nonempty (Representation.Equiv (ρRM.comp k) (ρ.comp k)) := by
  intro x FRM ρRM ρ k hirred
  obtain ⟨γ, c, b, ⟨hinertia, ζ, horientation, hlabel⟩, hmatrices⟩ :=
    darmonLabelledMonodromy_cusp_matrices N hN p L hL σ
  have hRM : ProjectiveLine.HasStandardLocalMonodromy N L σ FRM γ := by
    unfold ProjectiveLine.HasStandardLocalMonodromy
    intro i
    exact ⟨b, hmatrices i⟩
  exact ProjectiveLine.geometricEquiv_of_standard_localMonodromy_charZero N L σ hN p
    FRM F γ c ζ hinertia horientation hlabel hRM
    (hlocal γ c ζ hinertia horientation hlabel)
    (darmonLabelledMonodromy_arithmeticKernel_isIrreducible N hN p L hL σ) hirred


/-- Compatibility with the earlier odd-coefficient API. -/
theorem darmonLabelledMonodromy_geometricEquiv_of_localMonodromy
    (N : ℕ) [NeZero N] (hN : 3 ≤ N) (p : ℕ) [Fact p.Prime] (_hp : p ≠ 2)
    (L : Type) [NontriviallyNormedField L] [NormedAlgebra ℚ_[p] L]
    [FiniteDimensional ℚ_[p] L] [Algebra ℚ L] [IsScalarTower ℚ ℚ_[p] L]
    (hL : ∀ a : realCyclotomicField N, ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (σ : realCyclotomicField N →ₐ[ℚ] L)
    (F : Scheme.EtaleLocalSystem (RatFunc (realCyclotomicField N))
      (ProjectiveLine.punctured (realCyclotomicField N)) L)
    (hlocal : ∀
      (γ c : Fin 3 → AlgebraicClosure (RatFunc (realCyclotomicField N)) ≃ₐ[
        RatFunc (realCyclotomicField N)] AlgebraicClosure (RatFunc (realCyclotomicField N)))
      (ζ : ℕ → AlgebraicClosure (RatFunc (realCyclotomicField N))),
      (∀ i, (Subgroup.zpowers (γ i)).topologicalClosure =
        (![RatFunc.affineInertia (realCyclotomicField N) 0,
           RatFunc.affineInertia (realCyclotomicField N) 1,
           RatFunc.infinityInertia (realCyclotomicField N)] i).map
             (MulAut.conj (c i)).toMonoidHom) →
      ProjectiveLine.HasCommonCuspOrientation (realCyclotomicField N) γ ζ →
      ζ N + (ζ N)⁻¹ = algebraMap (realCyclotomicField N) _ (tau N 1) →
      ProjectiveLine.HasStandardLocalMonodromy N L σ F γ) :
    let x := ProjectiveLine.puncturedRationalPoint (realCyclotomicField N)
    let FRM := GroupScheme.labelledTateEtaleLocalSystem (RatFunc (realCyclotomicField N))
      (darmonFamily N hN) p L (realCyclotomicField N)
      (darmonRealMultiplication N hN) hL σ
    let ρRM := Scheme.fiberMonodromy (RatFunc (realCyclotomicField N))
      (ProjectiveLine.punctured (realCyclotomicField N)) FRM.algebraicFunctor x
    let ρ := Scheme.fiberMonodromy (RatFunc (realCyclotomicField N))
      (ProjectiveLine.punctured (realCyclotomicField N)) F.algebraicFunctor x
    let k := (Scheme.etaleFundamentalGroupMap
      (ProjectiveLine.puncturedToSpec (realCyclotomicField N))
      (RatFunc (realCyclotomicField N)) x).ker.subtype
    Representation.IsIrreducible (ρ.comp k) →
      Nonempty (Representation.Equiv (ρRM.comp k) (ρ.comp k)) := by
  exact darmonLabelledMonodromy_geometricEquiv_of_localMonodromy_charZero N hN p L hL σ F hlocal

/-- The actual chosen labelled Darmon family and its continuous cohomological
dual agree geometrically. All cusp and irreducibility hypotheses are derived
from the chosen realization, with no arithmetic determinant assumption. -/
theorem darmonLabelledMonodromy_geometricEquiv_cohDual_charZero
    (N : ℕ) [NeZero N] (hN : 3 ≤ N) (p : ℕ) [Fact p.Prime]
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
    [Algebra ℚ L] [IsScalarTower ℚ ℚ_[p] L]
    (hL : ∀ a : realCyclotomicField N, ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (σ : realCyclotomicField N →ₐ[ℚ] L) :
    let x := ProjectiveLine.puncturedRationalPoint (realCyclotomicField N)
    let F := GroupScheme.labelledTateEtaleLocalSystem (RatFunc (realCyclotomicField N))
      (darmonFamily N hN) p L (realCyclotomicField N)
      (darmonRealMultiplication N hN) hL σ
    let ρ := Scheme.fiberMonodromy (RatFunc (realCyclotomicField N))
      (ProjectiveLine.punctured (realCyclotomicField N)) F.algebraicFunctor x
    let ρdual := Scheme.fiberMonodromy (RatFunc (realCyclotomicField N))
      (ProjectiveLine.punctured (realCyclotomicField N)) F.cohDual.algebraicFunctor x
    let k := (Scheme.etaleFundamentalGroupMap
      (ProjectiveLine.puncturedToSpec (realCyclotomicField N))
      (RatFunc (realCyclotomicField N)) x).ker.subtype
    Nonempty (Representation.Equiv (ρ.comp k) (ρdual.comp k)) := by
  intro x F ρ ρdual k
  obtain ⟨γ, c, b, ⟨hinertia, ζ, horientation, hlabel⟩, hmatrices⟩ :=
    darmonLabelledMonodromy_cusp_matrices N hN p L hL σ
  have hF : ProjectiveLine.HasStandardLocalMonodromy N L σ F γ :=
    fun i => ⟨b, hmatrices i⟩
  exact ProjectiveLine.geometricEquiv_cohDual_of_standard_localMonodromy_charZero
    N hN p L σ F γ c ζ hinertia horientation hlabel hF
    (darmonLabelledMonodromy_arithmeticKernel_isIrreducible N hN p L hL σ)


/-- Compatibility with the earlier odd-coefficient API. -/
theorem darmonLabelledMonodromy_geometricEquiv_cohDual
    (N : ℕ) [NeZero N] (hN : 3 ≤ N) (p : ℕ) [Fact p.Prime] (_hp : p ≠ 2)
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
    [Algebra ℚ L] [IsScalarTower ℚ ℚ_[p] L]
    (hL : ∀ a : realCyclotomicField N, ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (σ : realCyclotomicField N →ₐ[ℚ] L) :
    let x := ProjectiveLine.puncturedRationalPoint (realCyclotomicField N)
    let F := GroupScheme.labelledTateEtaleLocalSystem (RatFunc (realCyclotomicField N))
      (darmonFamily N hN) p L (realCyclotomicField N)
      (darmonRealMultiplication N hN) hL σ
    let ρ := Scheme.fiberMonodromy (RatFunc (realCyclotomicField N))
      (ProjectiveLine.punctured (realCyclotomicField N)) F.algebraicFunctor x
    let ρdual := Scheme.fiberMonodromy (RatFunc (realCyclotomicField N))
      (ProjectiveLine.punctured (realCyclotomicField N)) F.cohDual.algebraicFunctor x
    let k := (Scheme.etaleFundamentalGroupMap
      (ProjectiveLine.puncturedToSpec (realCyclotomicField N))
      (RatFunc (realCyclotomicField N)) x).ker.subtype
    Nonempty (Representation.Equiv (ρ.comp k) (ρdual.comp k)) := by
  exact darmonLabelledMonodromy_geometricEquiv_cohDual_charZero N hN p L hL σ

end HilbertModularity.Hypergeometric
