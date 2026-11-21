/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.HypergeometricCohomology
public import HilbertModularity.Hypergeometric.PrimePlusSelectedChecklist

/-! # Finite ramification of the chosen Darmon cohomological fibres

The general abelian-variety good-reduction input gives a finite exceptional set
for the integral Tate module. Rationalization, extension of coefficients,
restriction to the fixed coefficient label and contragredient duality preserve
inertia triviality. This supplies the RM-side ramification hypothesis in the
arithmetic comparison of [TripathiGoswamiRevised, Theorem RMgeneral].
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry IsDedekindDomain
open scoped CategoryTheory.MonObj NumberField TensorProduct

private theorem representation_eq_one_of_equiv
    {R G V W : Type*} [CommRing R] [Group G]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    {ρ : Representation R G V} {τ : Representation R G W}
    (e : ρ.Equiv τ) (g : G) (h : τ g = 1) : ρ g = 1 := by
  apply LinearMap.ext
  intro v
  apply e.toLinearEquiv.injective
  exact (Representation.IntertwiningMap.isIntertwining ρ τ e.toIntertwiningMap g v).trans
    (congrArg (fun f => f (e v)) h)

namespace AlgebraicGeometry.GroupScheme

/-- Triviality on integral Tate vectors implies triviality on the rational Tate module. -/
theorem tateRepresentation_apply_eq_self_of_integral
    (K : Type*) [Field K]
    (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
    (p : ℕ) [Fact p.Prime] (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (h : ∀ v : integralTate K A p, integralTateRepresentation K A p g v = v)
    (v : rationalTate K A p) : tateRepresentation K A p g v = v := by
  induction v using TensorProduct.inductionOn with
  | tmul c v => rw [tateRepresentation_tmul, h]
  | add v w hv hw => rw [map_add, hv, hw]

/-- Inertia triviality passes to the dual of each fixed coefficient-labelled factor.
The inverse occurs because the dual action is contragredient. -/
theorem labelledDualTateFactor_apply_eq_self_of_integral
    (K : Type*) [Field K]
    (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
    (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [NumberField F]
    (L : Type*) [Field L] [Algebra ℚ_[p] L] [Algebra ℚ L]
    (hL : ∀ a : F, ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (φ : 𝓞 F →+* AddMonoid.End (Points K (AlgebraicClosure K) A))
    (hφ : ∀ a, ∃ (f : A ⟶ A) (_ : IsMonHom f),
      φ a = pointsMap K (AlgebraicClosure K) f)
    (σ : F →ₐ[ℚ] L) (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (h : ∀ v : integralTate K A p, integralTateRepresentation K A p g⁻¹ v = v)
    (v : Module.Dual L (labelledTateSummand K A p F L hL φ σ)) :
    labelledDualTateFactor K A p F L hL φ hφ σ g v = v := by
  have hrat : tateRepresentation K A p g⁻¹ = 1 :=
    LinearMap.ext (tateRepresentation_apply_eq_self_of_integral K A p g⁻¹ h)
  have hext : (tateRepresentation K A p).baseChange L g⁻¹ = 1 := by
    change (tateRepresentation K A p g⁻¹).baseChange L = 1
    rw [hrat, LinearMap.baseChange_one]
  have hsub : (labelledTateSubrepresentation K A p F L hL φ hφ σ).toRepresentation
      g⁻¹ = 1 := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    change (tateRepresentation K A p).baseChange L g⁻¹ w.val = w.val
    rw [hext]
    rfl
  change v.comp ((labelledTateSubrepresentation K A p F L hL φ hφ σ).toRepresentation
    g⁻¹) = v
  rw [hsub]
  rfl

end AlgebraicGeometry.GroupScheme

namespace HilbertModularity.Hypergeometric

open HilbertModularity.Cyclotomic GroupScheme

/-- Every actual nonsingular Darmon cohomological fibre is unramified outside
a finite set of number-field places. The exceptional set comes from the same
abelian variety's integral Tate module, using the named good-reduction input
[MilneAV, Chapter IV, §3, Theorem 3.5] and its documented spreading-out step.
The coefficient embedding is unchanged by taking the dual. -/
theorem darmonCohomologicalFamily_unramifiedOutsideFinite
    (K : Type) [Field K] [NumberField K] (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (p : ℕ) [Fact p.Prime] (m : ℕ) (hm : m.Coprime N)
    (E : IntermediateField ℚ Qbar) [NumberField E]
    (hE : IntermediateField.normalClosure ℚ (realCyclotomicField N) Qbar ≤ E)
    (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver (Ideal.span {(p : ℤ)})]
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra (w.adicCompletion E) L] [ContinuousSMul (w.adicCompletion E) L]
    [Algebra ℚ_[p] L] [IsScalarTower ℚ_[p] (w.adicCompletion E) L]
    [Algebra ℚ L] [IsScalarTower ℚ (w.adicCompletion E) L]
    (x : Spec (CommRingCat.of K) ⟶ ProjectiveLine.punctured (realCyclotomicField N)) :
    ∃ ramified : Set (HeightOneSpectrum (𝓞 K)), ramified.Finite ∧
      ∀ q, q ∉ ramified →
        ∀ (P : Ideal (𝓞 K)) [P.IsMaximal], P = q.asIdeal →
        ∀ (Q : Ideal (𝓞 (AlgebraicClosure K))) [Q.IsMaximal] [Q.LiesOver P],
        ∀ g : HilbertModularForms.AbsoluteGalois K,
          g ∈ Q.inertia (HilbertModularForms.AbsoluteGalois K) →
            (darmonCohomologicalFamily K N hN p m hm E hE w L).arithmeticRepresentation
              x g = 1 := by
  have : IsProper (fiber K (darmonFamily N hN) x).X.hom :=
    fiber_isProper K (darmonFamily N hN) x
  have : Smooth (fiber K (darmonFamily N hN) x).X.hom :=
    letI : Smooth (darmonFamily N hN).X.hom :=
      (darmonFamily_smoothOfRelativeDimension N hN).smooth
    fiber_smooth K (darmonFamily N hN) x
  have : GeometricallyConnected (fiber K (darmonFamily N hN) x).X.hom :=
    fiber_geometricallyConnected K (darmonFamily N hN) x
  obtain ⟨ramified, hfinite, hnative⟩ :=
    abelianVariety_integralTate_unramifiedOutsideFinite K (fiber K (darmonFamily N hN) x) p
  refine ⟨ramified, hfinite, ?_⟩
  intro q hq P _ hP Q _ _ g hg
  apply representation_eq_one_of_equiv
    (darmonCohomologicalFamilyArithmeticEquiv K N hN p m hm E hE w L x) g
  exact LinearMap.ext (labelledDualTateFactor_apply_eq_self_of_integral K
    (fiber K (darmonFamily N hN) x).X p (realCyclotomicField N) L
    (splits_minpoly_above_coefficientPrime N E w L hE)
    (fiberPointsAction K (AlgebraicClosure K) (darmonFamily N hN) x
      (𝓞 (realCyclotomicField N)) (darmonRealMultiplication N hN))
    (fiberPointsAction_realized K (AlgebraicClosure K) (darmonFamily N hN) x
      (𝓞 (realCyclotomicField N)) (darmonRealMultiplication N hN))
    (coefficientEmbeddingAbovePrime N m hm E
      ((IntermediateField.le_normalClosure (realCyclotomicField N)).trans hE) w L) g
    (hnative q hq P hP Q g⁻¹ ((Q.inertia _).inv_mem hg)))

end HilbertModularity.Hypergeometric
