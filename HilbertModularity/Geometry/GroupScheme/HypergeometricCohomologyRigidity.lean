/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.HypergeometricRigidity
public import HilbertModularity.Geometry.GroupScheme.HypergeometricCohomologyIrreducibility
public import HilbertModularity.RepresentationTheory.Duality

/-! # Fixed-label cohomological comparison from local monodromy

Apply [DarmonFibres, Proposition 2.4] to the chosen cohomological factor,
retaining its coefficient prime and exponent label. Geometric paths then carry
the comparison to the arithmetic kernel used in the all-fibre descent argument
of [TripathiGoswamiRevised, proof of Theorem RMgeneral, steps 2–3].
The effective family's local classes and its actual path comparison remain
explicit inputs; this does not assert them for an unconstructed Euler family.
-/

public noncomputable section
open CategoryTheory AlgebraicGeometry IsDedekindDomain
open scoped NumberField CategoryTheory.MonObj
namespace HilbertModularity.Hypergeometric
open _root_.HilbertModularity.Cyclotomic

variable (N : ℕ) [NeZero N] (hN : 3 ≤ N)
  (p : ℕ) [Fact p.Prime] (m : ℕ) (hm : m.Coprime N)
  (E : IntermediateField ℚ Qbar) [NumberField E]
  (hE : IntermediateField.normalClosure ℚ (realCyclotomicField N) Qbar ≤ E)
  (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver (Ideal.span {(p : ℤ)})]
  (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
  [Algebra (w.adicCompletion E) L] [ContinuousSMul (w.adicCompletion E) L]
  [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
  [IsScalarTower ℚ_[p] (w.adicCompletion E) L]
  [Algebra ℚ L] [IsScalarTower ℚ (w.adicCompletion E) L]

/-- The actual cohomological Darmon factor compares geometrically with any
irreducible local system having the same oriented cusp classes. The duality and
coefficient specialization are deduced, with the prescribed label unchanged. -/
theorem darmonCohomologicalFamily_geometricEquiv_of_localMonodromy_charZero
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
      ProjectiveLine.HasStandardLocalMonodromy N L
        (coefficientEmbeddingAbovePrime N m hm E
          ((IntermediateField.le_normalClosure (realCyclotomicField N)).trans hE) w L) F γ) :
    let x := ProjectiveLine.puncturedRationalPoint (realCyclotomicField N)
    let ρRM := Scheme.fiberMonodromy (RatFunc (realCyclotomicField N))
      (ProjectiveLine.punctured (realCyclotomicField N))
      (darmonCohomologicalFamily (RatFunc (realCyclotomicField N))
        N hN p m hm E hE w L).algebraicFunctor x
    let ρ := Scheme.fiberMonodromy (RatFunc (realCyclotomicField N))
      (ProjectiveLine.punctured (realCyclotomicField N)) F.algebraicFunctor x
    let k := (Scheme.etaleFundamentalGroupMap
      (ProjectiveLine.puncturedToSpec (realCyclotomicField N))
      (RatFunc (realCyclotomicField N)) x).ker.subtype
    Representation.IsIrreducible (ρ.comp k) →
      Nonempty (Representation.Equiv (ρRM.comp k) (ρ.comp k)) := by
  intro x ρRM ρ k hirred
  let : IsScalarTower ℚ ℚ_[p] L :=
    IsScalarTower.to₁₂₄ ℚ ℚ_[p] (w.adicCompletion E) L
  let σ := coefficientEmbeddingAbovePrime N m hm E
    ((IntermediateField.le_normalClosure (realCyclotomicField N)).trans hE) w L
  let hL := splits_minpoly_above_coefficientPrime N E w L hE
  obtain ⟨eDual⟩ := darmonLabelledMonodromy_geometricEquiv_cohDual_charZero N hN p L hL σ
  obtain ⟨eEff⟩ := darmonLabelledMonodromy_geometricEquiv_of_localMonodromy_charZero
    N hN p L hL σ F hlocal hirred
  exact ⟨eDual.symm.trans eEff⟩


/-- Compatibility with the earlier odd-coefficient API. -/
theorem darmonCohomologicalFamily_geometricEquiv_of_localMonodromy
    (_hp : p ≠ 2)
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
      ProjectiveLine.HasStandardLocalMonodromy N L
        (coefficientEmbeddingAbovePrime N m hm E
          ((IntermediateField.le_normalClosure (realCyclotomicField N)).trans hE) w L) F γ) :
    let x := ProjectiveLine.puncturedRationalPoint (realCyclotomicField N)
    let ρRM := Scheme.fiberMonodromy (RatFunc (realCyclotomicField N))
      (ProjectiveLine.punctured (realCyclotomicField N))
      (darmonCohomologicalFamily (RatFunc (realCyclotomicField N))
        N hN p m hm E hE w L).algebraicFunctor x
    let ρ := Scheme.fiberMonodromy (RatFunc (realCyclotomicField N))
      (ProjectiveLine.punctured (realCyclotomicField N)) F.algebraicFunctor x
    let k := (Scheme.etaleFundamentalGroupMap
      (ProjectiveLine.puncturedToSpec (realCyclotomicField N))
      (RatFunc (realCyclotomicField N)) x).ker.subtype
    Representation.IsIrreducible (ρ.comp k) →
      Nonempty (Representation.Equiv (ρRM.comp k) (ρ.comp k)) := by
  exact darmonCohomologicalFamily_geometricEquiv_of_localMonodromy_charZero N hN p m hm E hE w L F hlocal

/-- The actual chosen cohomological factor transports along the generic-to-fibre
path, preserving the coefficient prime and embedding. -/
def darmonCohomologicalFamilyGeometricPathEquiv
    (x : Spec (CommRingCat.of (realCyclotomicField N)) ⟶
      ProjectiveLine.punctured (realCyclotomicField N)) :
    Representation.Equiv
      (Scheme.fiberMonodromy (RatFunc (realCyclotomicField N))
        (ProjectiveLine.punctured (realCyclotomicField N))
        (darmonCohomologicalFamily (RatFunc (realCyclotomicField N))
          N hN p m hm E hE w L).algebraicFunctor
        (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N)))
      ((Scheme.fiberMonodromy (realCyclotomicField N)
        (ProjectiveLine.punctured (realCyclotomicField N))
        (darmonCohomologicalFamily (realCyclotomicField N)
          N hN p m hm E hE w L).algebraicFunctor x).comp
        (Scheme.geometricFiberPathGroupEquiv _ _
          (ProjectiveLine.puncturedGenericFiberPath (realCyclotomicField N) x)).toMonoidHom) := by
  let σ := coefficientEmbeddingAbovePrime N m hm E
    ((IntermediateField.le_normalClosure (realCyclotomicField N)).trans hE) w L
  let hL := splits_minpoly_above_coefficientPrime N E w L hE
  let e := GroupScheme.labelledTateGeometricPathRepresentationEquiv
    (RatFunc (realCyclotomicField N)) (realCyclotomicField N)
    (ProjectiveLine.puncturedGenericFiberPath (realCyclotomicField N) x)
    (darmonFamily N hN) p L (realCyclotomicField N)
    (darmonRealMultiplication N hN) hL σ
  change Representation.Equiv
    (Scheme.fiberMonodromy _ _ (ModuleCat.cohDual L _) _)
    ((Scheme.fiberMonodromy _ _ (ModuleCat.cohDual L _) _).comp _)
  rw [Scheme.fiberMonodromy_cohDual, Scheme.fiberMonodromy_cohDual]
  let ρ₁ := Scheme.fiberMonodromy (RatFunc (realCyclotomicField N))
    (ProjectiveLine.punctured (realCyclotomicField N))
    (GroupScheme.labelledTateLocalSystem (RatFunc (realCyclotomicField N))
      (darmonFamily N hN) p L (realCyclotomicField N)
      (darmonRealMultiplication N hN) hL σ)
    (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N))
  let ρ₂ := Scheme.fiberMonodromy (realCyclotomicField N)
    (ProjectiveLine.punctured (realCyclotomicField N))
    (GroupScheme.labelledTateLocalSystem (realCyclotomicField N)
      (darmonFamily N hN) p L (realCyclotomicField N)
      (darmonRealMultiplication N hN) hL σ) x
  let f := (Scheme.geometricFiberPathGroupEquiv _ _
    (ProjectiveLine.puncturedGenericFiberPath (realCyclotomicField N) x)).toMonoidHom
  change Representation.Equiv ρ₁.dual (ρ₂.dual.comp f)
  let d := representationDualEquiv e
  refine .mk d.toLinearEquiv ?_
  intro g
  have h := d.isIntertwining' g
  change d.toLinearEquiv.toLinearMap ∘ₗ (ρ₁ g⁻¹).dualMap =
    (ρ₂ ((f g)⁻¹)).dualMap ∘ₗ d.toLinearEquiv.toLinearMap
  change d.toLinearEquiv.toLinearMap ∘ₗ (ρ₁ g⁻¹).dualMap =
    (ρ₂ (f g⁻¹)).dualMap ∘ₗ d.toLinearEquiv.toLinearMap at h
  rw [f.map_inv] at h
  exact h

omit [FiniteDimensional ℚ_[p] L] in
/-- A geometric comparison at the generic point gives the comparison on the
rational arithmetic kernel used in descent. The effective family's path
compatibility is explicit: two unrelated local systems cannot be identified
merely by calling both of them the effective family. -/
theorem darmonCohomologicalFamily_arithmeticKernel_equiv_of_generic
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    (F : Scheme.EtaleLocalSystem (RatFunc (realCyclotomicField N))
      (ProjectiveLine.punctured (realCyclotomicField N)) L)
    (G : Scheme.EtaleLocalSystem (realCyclotomicField N)
      (ProjectiveLine.punctured (realCyclotomicField N)) L) :
    let x := ProjectiveLine.puncturedPoint (realCyclotomicField N) ξ
    let xgen := ProjectiveLine.puncturedRationalPoint (realCyclotomicField N)
    let path := ProjectiveLine.puncturedGenericFiberPath (realCyclotomicField N) x
    let ρF := Scheme.fiberMonodromy (RatFunc (realCyclotomicField N))
      (ProjectiveLine.punctured (realCyclotomicField N)) F.algebraicFunctor xgen
    let ρG := puncturedFiberMonodromy (realCyclotomicField N) ξ G
    let ρRM := Scheme.fiberMonodromy (RatFunc (realCyclotomicField N))
      (ProjectiveLine.punctured (realCyclotomicField N))
      (darmonCohomologicalFamily (RatFunc (realCyclotomicField N))
        N hN p m hm E hE w L).algebraicFunctor xgen
    let k := (Scheme.etaleFundamentalGroupMap
      (ProjectiveLine.puncturedToSpec (realCyclotomicField N))
      (RatFunc (realCyclotomicField N)) xgen).ker.subtype
    Representation.Equiv ρF
      (ρG.comp (Scheme.geometricFiberPathGroupEquiv _ _ path).toMonoidHom) →
    Representation.Equiv (ρRM.comp k) (ρF.comp k) →
    Nonempty (Representation.Equiv
      ((puncturedFiberMonodromy (realCyclotomicField N) ξ
        (darmonCohomologicalFamily (realCyclotomicField N)
          N hN p m hm E hE w L)).comp
        (puncturedArithmeticProjectionHom (realCyclotomicField N) ξ).ker.subtype)
      (ρG.comp (puncturedArithmeticProjectionHom (realCyclotomicField N) ξ).ker.subtype)) := by
  intro x xgen path ρF ρG ρRM k ePath eGeom
  let eRM := darmonCohomologicalFamilyGeometricPathEquiv N hN p m hm E hE w L x
  let ek := Scheme.geometricFiberPathKernelEquiv
    (ProjectiveLine.puncturedToSpec (realCyclotomicField N))
    (RatFunc (realCyclotomicField N)) (realCyclotomicField N) path
  let e := (eRM.compHom k).symm.trans (eGeom.trans (ePath.compHom k))
  rw [puncturedArithmeticProjectionHom_ker]
  refine ⟨Representation.Equiv.ofCompSurjective ek.toMonoidHom ek.surjective ?_⟩
  refine .mk e.toLinearEquiv ?_
  intro g
  have h := e.isIntertwining' g
  change e.toLinearEquiv.toLinearMap ∘ₗ
      (puncturedFiberMonodromy (realCyclotomicField N) ξ
        (darmonCohomologicalFamily (realCyclotomicField N)
          N hN p m hm E hE w L)) (ek g).val =
    ρG (ek g).val ∘ₗ e.toLinearEquiv.toLinearMap
  dsimp only [ek]
  rw [Scheme.geometricFiberPathKernelEquiv_coe]
  exact h

end HilbertModularity.Hypergeometric
