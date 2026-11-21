/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.PrimePlusNativeLocalAction
public import HilbertModularity.NumberTheory.RealCyclotomicResidue

/-! # Decomposition groups at the selected real cyclotomic prime

The fixed embedding of the global algebraic closure into the local algebraic
closure selects one prime above `p`. A different prime gives a conjugate
decomposition subgroup. Keeping this conjugacy explicit is necessary when the
Skinner–Wiles checklist ranges over every prime above `p`.
-/

public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.GroupScheme
open scoped NumberField ValuativeRel

namespace HilbertModularity.Hypergeometric

open HilbertModularity.Cyclotomic HilbertModularity.HilbertModularForms ValuativeRel

attribute [local instance] realPrimePowerCompletionPadicAlgebra
  realPrimePowerCompletionPadicTower

/-- [MilneANT, Proposition 8.10 and the inertia diagram, pp. 139–140;
Proposition 8.13, p. 141; MilneFT, Theorem 7.13] For every prime `Q` of
the global algebraic closure above the unique prime of `Kₚ`, its decomposition
group is conjugate to the image of the chosen local Galois restriction. The
conjugating element depends on `Q`, because the existing embedding into
`PadicAlgCl` is fixed independently of `Q`. The equivalence is continuous and
matches inertia. This is a standard local/global Galois comparison; it does
not assert ordinary reduction or a representation isomorphism. -/
theorem exists_primePlusDecompositionEquiv
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p))))
    [Q.IsMaximal]
    [Q.LiesOver (realPrimeAboveConductor p).asIdeal] :
    ∃ (σ : AbsoluteGalois (realCyclotomicField p))
      (δ : primeDecompositionGroup Q ≃*
        Gal(PadicAlgCl p/RealPrimePowerCompletion p 0)),
      Continuous δ ∧
      (∀ g : primeDecompositionGroup Q,
        primePlusLocalGaloisRestriction p (δ g) =
          σ * (g : AbsoluteGalois (realCyclotomicField p)) * σ⁻¹) ∧
      (∀ g : primeDecompositionGroup Q,
        (g : AbsoluteGalois (realCyclotomicField p)) ∈
          Q.inertia (AbsoluteGalois (realCyclotomicField p)) ↔
        δ g ∈ PadicAlgCl.inertia p (RealPrimePowerCompletion p 0)) := by
  sorry

/-- The native selected coordinate action at an arbitrary prime `Q` agrees
with the local action after conjugating global coordinates by the element
that moves `Q` to the prime selected by the fixed completion embedding. This
is the operator deduction from the standard decomposition equivalence. -/
theorem primePlusTateFieldCoordinate_conjugatedDecompositionIntertwines
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    [ValuativeRel (RealPrimePowerCompletion p 0)]
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) (RealPrimePowerCompletion p 0)]
    (β : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[RealPrimePowerCompletion p 0])
    (hβ : (inferInstance : Algebra (AdicCompletion
      (Ideal.span {realPrimeGenerator p}) (𝓞 (realCyclotomicField p)))
      (RealPrimePowerCompletion p 0)) =
        ((𝒪[RealPrimePowerCompletion p 0]).subtype.comp β).toAlgebra)
    (e : letI := primePlusIntegralTateModule p hp ξ
      letI : Algebra (RealPrimePowerCompletion p 0)
        (RealPrimePowerCompletion p 0) :=
          (AlgHom.id ℚ_[p] (RealPrimePowerCompletion p 0)).toAlgebra
      ((primePlusLocalTateRepresentation p hp ξ).ρ.baseChange
        (RealPrimePowerCompletion p 0)).Equiv
        ((primePlusIntegralTateRepresentation p hp ξ).baseChange
          (RealPrimePowerCompletion p 0)))
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p))))
    [Q.IsMaximal]
    (σ : AbsoluteGalois (realCyclotomicField p))
    (δ : primeDecompositionGroup Q →*
      Gal(PadicAlgCl p/RealPrimePowerCompletion p 0))
    (hδ : ∀ g : primeDecompositionGroup Q,
      primePlusLocalGaloisRestriction p (δ g) =
        σ * (g : AbsoluteGalois (realCyclotomicField p)) * σ⁻¹)
    (g : primeDecompositionGroup Q) (v : Fin 2 → RealPrimePowerCompletion p 0) :
    let E := primePlusTateFieldCoordinateNativeEquiv p hp ξ β hβ e
    let ρ := primePlusTateFieldCoordinateAction p hp ξ β
    E (ρ σ (ρ (g : AbsoluteGalois (realCyclotomicField p)) v)) =
      (primePlusLocalTateRepresentation p hp ξ).ρ
        (primePlusLocalGaloisRestriction p (δ g)) (E (ρ σ v)) := by
  let E := primePlusTateFieldCoordinateNativeEquiv p hp ξ β hβ e
  let ρ := primePlusTateFieldCoordinateAction p hp ξ β
  have h := LinearMap.congr_fun
    (E.toIntertwiningMap.isIntertwining'
      (σ * (g : AbsoluteGalois (realCyclotomicField p)) * σ⁻¹)) (ρ σ v)
  change E (ρ (σ * (g : AbsoluteGalois (realCyclotomicField p)) * σ⁻¹)
      (ρ σ v)) =
    (primePlusLocalTateRepresentation p hp ξ).ρ
      (σ * (g : AbsoluteGalois (realCyclotomicField p)) * σ⁻¹)
      (E (ρ σ v)) at h
  have hleft : ρ (σ * (g : AbsoluteGalois (realCyclotomicField p)) * σ⁻¹)
      (ρ σ v) = ρ σ (ρ (g : AbsoluteGalois (realCyclotomicField p)) v) := by
    calc
      ρ (σ * (g : AbsoluteGalois (realCyclotomicField p)) * σ⁻¹) (ρ σ v) =
          (ρ (σ * (g : AbsoluteGalois (realCyclotomicField p)) * σ⁻¹) * ρ σ) v := by
            rw [Module.End.mul_apply]
      _ = ρ ((σ * (g : AbsoluteGalois (realCyclotomicField p)) * σ⁻¹) * σ) v := by
        simp only [map_mul, Module.End.mul_apply]
      _ = ρ (σ * (g : AbsoluteGalois (realCyclotomicField p))) v := by
        congr 1
        group
      _ = ρ σ (ρ (g : AbsoluteGalois (realCyclotomicField p)) v) := by
        rw [map_mul, Module.End.mul_apply]
  rw [hleft] at h
  rw [← hδ g] at h
  exact h

/-- The actual selected native Tate action at every chosen prime above `p`
has a continuous local decomposition action, with the conjugation dictated by
the fixed algebraic-closure embedding. Its inertia subset is transported by
the same map. The only admission used is the named standard local/global
Galois comparison above; the operator identity is proved here. -/
theorem exists_primePlusTateFieldCoordinate_conjugatedLocalAction
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    [ValuativeRel (RealPrimePowerCompletion p 0)]
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) (RealPrimePowerCompletion p 0)]
    (β : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[RealPrimePowerCompletion p 0])
    (hβ : (inferInstance : Algebra (AdicCompletion
      (Ideal.span {realPrimeGenerator p}) (𝓞 (realCyclotomicField p)))
      (RealPrimePowerCompletion p 0)) =
        ((𝒪[RealPrimePowerCompletion p 0]).subtype.comp β).toAlgebra)
    (e : letI := primePlusIntegralTateModule p hp ξ
      letI : Algebra (RealPrimePowerCompletion p 0)
        (RealPrimePowerCompletion p 0) :=
          (AlgHom.id ℚ_[p] (RealPrimePowerCompletion p 0)).toAlgebra
      ((primePlusLocalTateRepresentation p hp ξ).ρ.baseChange
        (RealPrimePowerCompletion p 0)).Equiv
        ((primePlusIntegralTateRepresentation p hp ξ).baseChange
          (RealPrimePowerCompletion p 0)))
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p))))
    [Q.IsMaximal]
    [Q.LiesOver (realPrimeAboveConductor p).asIdeal] :
    ∃ (σ : AbsoluteGalois (realCyclotomicField p))
      (δ : primeDecompositionGroup Q ≃*
        Gal(PadicAlgCl p/RealPrimePowerCompletion p 0)),
      Continuous δ ∧
      (∀ g : primeDecompositionGroup Q,
        (g : AbsoluteGalois (realCyclotomicField p)) ∈
          Q.inertia (AbsoluteGalois (realCyclotomicField p)) ↔
        δ g ∈ PadicAlgCl.inertia p (RealPrimePowerCompletion p 0)) ∧
      (∀ (g : primeDecompositionGroup Q)
        (v : Fin 2 → RealPrimePowerCompletion p 0),
        let E := primePlusTateFieldCoordinateNativeEquiv p hp ξ β hβ e
        let ρ := primePlusTateFieldCoordinateAction p hp ξ β
        E (ρ σ (ρ (g : AbsoluteGalois (realCyclotomicField p)) v)) =
          (primePlusLocalTateRepresentation p hp ξ).ρ
            (primePlusLocalGaloisRestriction p (δ g)) (E (ρ σ v))) := by
  obtain ⟨σ, δ, hcont, hδ, hInertia⟩ := exists_primePlusDecompositionEquiv p hp Q
  refine ⟨σ, δ, hcont, hInertia, ?_⟩
  intro g v
  exact primePlusTateFieldCoordinate_conjugatedDecompositionIntertwines p hp ξ
    β hβ e Q σ δ.toMonoidHom hδ g v

end HilbertModularity.Hypergeometric
