/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.TateModule.GoodReduction
public import HilbertModularity.Geometry.TateModule.CoefficientTrace

/-! # Coefficient traces at good reduction

The integral basis of the RM field supplies algebraic endomorphisms. Their
common rational Frobenius traces feed the fixed coefficient projector, without
an auxiliary-prime-dependent choice of projector or rational endomorphism.
-/

public section
noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj NumberField TensorProduct

namespace AlgebraicGeometry.GroupScheme

universe u

variable (K : Type u) [Field K] [NumberField K]
  (P : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
  (B : CommGrp (Over (Spec (CommRingCat.of (P.valuationSubringAtPrime K)))))

/-- A good-reduction endomorphism has the same rational Frobenius power trace
after every extension of Tate coefficients. -/
theorem exists_goodReduction_frobeniusTrace_baseChange
    [IsProper B.X.hom] [Smooth B.X.hom] [GeometricallyConnected B.X.hom]
    (f : End (localGenericFiber K P B)) (n : ℕ) :
    ∃ t : ℚ,
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure K))) [Q.IsMaximal] [Q.LiesOver P.asIdeal]
        (p : ℕ) (hp : p.Prime) (_ : (p : 𝓞 K) ∉ P.asIdeal),
        letI : Fact p.Prime := ⟨hp⟩
        ∀ (_ : FiniteDimensional ℚ_[p] (rationalTate K (localGenericFiber K P B).X p))
          (L : Type*) [Field L] [Algebra ℚ_[p] L] [Algebra ℚ L]
          [IsScalarTower ℚ ℚ_[p] L],
          LinearMap.trace L _
            ((rationalTateEndomorphismMap K (localGenericFiber K P B) p f).baseChange L *
              ((tateRepresentation K (localGenericFiber K P B).X p).baseChange L
                (NumberField.arithmeticFrobenius K (AlgebraicClosure K) P.asIdeal Q)) ^ n) =
            algebraMap ℚ L t := by
  obtain ⟨t, ht⟩ := exists_goodReduction_weightedFrobeniusTrace K P B f 1 n
  refine ⟨t, ?_⟩
  intro Q _ _ p hp hpP
  let : Fact p.Prime := ⟨hp⟩
  intro hfinite L _ _ _ _
  let := hfinite
  let : Module.Free ℚ_[p] (rationalTate K (localGenericFiber K P B).X p) :=
    Module.Free.of_divisionRing _ _
  have h := ht Q p hp hpP hfinite
  simp only [map_one, one_smul] at h
  change LinearMap.trace L _
    ((rationalTateEndomorphismMap K (localGenericFiber K P B) p f).baseChange L *
      (tateRepresentation K (localGenericFiber K P B).X p
        (NumberField.arithmeticFrobenius K (AlgebraicClosure K) P.asIdeal Q)).baseChange L ^ n) = _
  rw [← LinearMap.baseChange_pow, ← LinearMap.baseChange_mul,
    LinearMap.trace_baseChange, h, ← IsScalarTower.algebraMap_apply]

/-- An integral RM coefficient acts through the endomorphism of the same
model, after extending the Tate scalars. -/
theorem tensorTateAction_localGenericFiber_integer
    (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [NumberField F]
    (L : Type*) [Field L] [Algebra ℚ_[p] L] [Algebra ℚ L]
    (ψ : 𝓞 F →+* End B) (a : 𝓞 F) :
    tensorTateAction K (localGenericFiber K P B).X p F L
      (fiberPointsAction K (AlgebraicClosure K) B (localGenericPoint K P) (𝓞 F) ψ)
      ((1 : L) ⊗ₜ[ℚ] (a : F)) =
    (rationalTateEndomorphismMap K (localGenericFiber K P B) p
      (fiberEndomorphismMap K B (localGenericPoint K P) (ψ a))).baseChange L := by
  rw [tensorTateAction_integer]
  congr 1
  rw [rationalTateEndomorphismMap_eq_rationalMap, fiberPointsAction_apply]

/-- Each integral RM coefficient has one rational Frobenius power trace,
independently of the auxiliary prime, scalar extension and Frobenius lift. -/
theorem exists_goodReduction_integralCoefficient_powerTrace
    [IsProper B.X.hom] [Smooth B.X.hom] [GeometricallyConnected B.X.hom]
    (F : Type*) [Field F] [NumberField F] (ψ : 𝓞 F →+* End B)
    (a : 𝓞 F) (n : ℕ) :
    ∃ t : ℚ,
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure K))) [Q.IsMaximal] [Q.LiesOver P.asIdeal]
        (p : ℕ) (hp : p.Prime) (_ : (p : 𝓞 K) ∉ P.asIdeal),
        letI : Fact p.Prime := ⟨hp⟩
        ∀ (_ : FiniteDimensional ℚ_[p] (rationalTate K (localGenericFiber K P B).X p))
          (L : Type*) [Field L] [Algebra ℚ_[p] L] [Algebra ℚ L]
          [IsScalarTower ℚ ℚ_[p] L],
          LinearMap.trace L _
            (tensorTateAction K (localGenericFiber K P B).X p F L
              (fiberPointsAction K (AlgebraicClosure K) B (localGenericPoint K P) (𝓞 F) ψ)
              ((1 : L) ⊗ₜ[ℚ] (a : F)) *
              ((tateRepresentation K (localGenericFiber K P B).X p).baseChange L
                (NumberField.arithmeticFrobenius K (AlgebraicClosure K) P.asIdeal Q)) ^ n) =
            algebraMap ℚ L t := by
  obtain ⟨t, ht⟩ := exists_goodReduction_frobeniusTrace_baseChange K P B
    (fiberEndomorphismMap K B (localGenericPoint K P) (ψ a)) n
  refine ⟨t, ?_⟩
  intro Q _ _ p hp hpP
  let : Fact p.Prime := ⟨hp⟩
  intro hfinite L _ _ _ _
  rw [tensorTateAction_localGenericFiber_integer]
  exact ht Q p hp hpP hfinite L

end AlgebraicGeometry.GroupScheme
