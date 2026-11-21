/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.PrimeHypergeometricResidual
public import HilbertModularity.Geometry.TateModule.GoodReductionIsomorphism

/-! # Inertia of the selected plus Jacobian at good reduction

The good-reduction specialization input is applied to the actual model of the
selected fibre, then transported through its generic-fibre isomorphism. No
additional ramification premise or literature admission is used.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped NumberField

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

private theorem baseChange_eq_one_of_eq_one
    {R L G V : Type*} [CommRing R] [CommRing L] [Algebra R L] [Monoid G]
    [AddCommGroup V] [Module R V] (ρ : Representation R G V)
    (g : G) (h : ρ g = 1) : ρ.baseChange L g = 1 := by
  change (ρ g).baseChange L = 1
  rw [h, LinearMap.baseChange_one]

private theorem subrepresentation_eq_one_of_eq_one
    {R G V : Type*} [CommRing R] [Monoid G]
    [AddCommGroup V] [Module R V] (ρ : Representation R G V)
    (S : Subrepresentation ρ) (g : G) (h : ρ g = 1) :
    S.toRepresentation g = 1 := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  change ρ g v.val = v.val
  rw [h]
  rfl

private theorem dual_eq_one_of_inv_eq_one
    {R G V : Type*} [CommSemiring R] [Group G]
    [AddCommMonoid V] [Module R V] (ρ : Representation R G V)
    (g : G) (h : ρ g⁻¹ = 1) : ρ.dual g = 1 := by
  apply LinearMap.ext
  intro v
  change v.comp (ρ g⁻¹) = v
  rw [h]
  rfl

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic GroupScheme

variable (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
  (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
  (P : IsDedekindDomain.HeightOneSpectrum (𝓞 (realCyclotomicField p)))
  (B : CommGrp (Over (Spec (CommRingCat.of
    (P.valuationSubringAtPrime (realCyclotomicField p))))))
  [IsProper B.X.hom] [Smooth B.X.hom] [GeometricallyConnected B.X.hom]
  (e : primePlusFiber p hp ξ ≅ localGenericFiber (realCyclotomicField p) P B)
  (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p))))
  [Q.IsMaximal] [Q.LiesOver P.asIdeal]
  (ℓ : ℕ) [Fact ℓ.Prime] (hℓP : (ℓ : 𝓞 (realCyclotomicField p)) ∉ P.asIdeal)

include e hℓP

/-- Inertia acts trivially on the selected Jacobian's rational Tate module at
any supplied good-reduction model, away from the residue characteristic.
This applies [MilneAV, Chapter IV, Theorem 3.5] to the same fibre. -/
theorem primePlusFiber_tate_inertia_eq_one
    (g : AlgebraicClosure (realCyclotomicField p) ≃ₐ[realCyclotomicField p]
      AlgebraicClosure (realCyclotomicField p))
    (hg : g ∈ Q.inertia (AlgebraicClosure (realCyclotomicField p) ≃ₐ[realCyclotomicField p]
      AlgebraicClosure (realCyclotomicField p))) :
    tateRepresentation (realCyclotomicField p) (primePlusFiber p hp ξ).X ℓ g = 1 := by
  have hs := exists_goodReductionTateSpecialization (realCyclotomicField p) P B
  rcases hs with ⟨Fr, hFr⟩
  have hsQ := hFr Q ℓ (Fact.out : ℓ.Prime) hℓP
  rcases hsQ with ⟨sp, hn, hf, hi⟩
  exact representation_eq_one_of_equiv
    (tateEquiv (realCyclotomicField p) ℓ e) g (hi g hg)

/-- The same inertia is trivial on every fixed-labelled Tate factor. Neither
scalar extension nor the RM coefficient projector changes the good prime. -/
theorem primePlusFiber_labelled_tate_inertia_eq_one
    (L : Type) [Field L] [Algebra ℚ_[ℓ] L] [Algebra ℚ L]
    [IsScalarTower ℚ ℚ_[ℓ] L]
    (hL : ∀ a : realCyclotomicField p,
      ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (σ : realCyclotomicField p →ₐ[ℚ] L)
    (g : AlgebraicClosure (realCyclotomicField p) ≃ₐ[realCyclotomicField p]
      AlgebraicClosure (realCyclotomicField p))
    (hg : g ∈ Q.inertia (AlgebraicClosure (realCyclotomicField p) ≃ₐ[realCyclotomicField p]
      AlgebraicClosure (realCyclotomicField p))) :
    (endomorphismLabelledTate (realCyclotomicField p) (primePlusFiber p hp ξ)
      ℓ (realCyclotomicField p) L hL (primePlusFiberRealMultiplication p hp ξ)
      σ).toRepresentation g = 1 := by
  have hrat := primePlusFiber_tate_inertia_eq_one p hp ξ P B e Q ℓ hℓP g hg
  have hext := baseChange_eq_one_of_eq_one (L := L)
    (tateRepresentation (realCyclotomicField p) (primePlusFiber p hp ξ).X ℓ) g hrat
  unfold endomorphismLabelledTate
  with_reducible
    exact subrepresentation_eq_one_of_eq_one _ _ g hext

/-- The cohomological dual of the selected labelled factor is unramified at
the same good prime. Inertia is a subgroup, so the inverse in the dual action
introduces no extra hypothesis. -/
theorem primePlusFiber_labelled_dual_inertia_eq_one
    (L : Type) [Field L] [Algebra ℚ_[ℓ] L] [Algebra ℚ L]
    [IsScalarTower ℚ ℚ_[ℓ] L]
    (hL : ∀ a : realCyclotomicField p,
      ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (σ : realCyclotomicField p →ₐ[ℚ] L)
    (g : AlgebraicClosure (realCyclotomicField p) ≃ₐ[realCyclotomicField p]
      AlgebraicClosure (realCyclotomicField p))
    (hg : g ∈ Q.inertia (AlgebraicClosure (realCyclotomicField p) ≃ₐ[realCyclotomicField p]
      AlgebraicClosure (realCyclotomicField p))) :
    (endomorphismLabelledTate (realCyclotomicField p) (primePlusFiber p hp ξ)
      ℓ (realCyclotomicField p) L hL (primePlusFiberRealMultiplication p hp ξ)
      σ).toRepresentation.dual g = 1 := by
  have hi := primePlusFiber_labelled_tate_inertia_eq_one p hp ξ P B e Q ℓ hℓP
    L hL σ g⁻¹ ((Q.inertia _).inv_mem hg)
  unfold endomorphismLabelledTate at hi ⊢
  apply dual_eq_one_of_inv_eq_one
  exact hi

end HilbertModularity.Hypergeometric
