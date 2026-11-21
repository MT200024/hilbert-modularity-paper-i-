/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.PlusCurveJacobian
public import HilbertModularity.Geometry.TateModule.GoodReduction

/-! # The standard good-reduction criterion for hyperelliptic Jacobians

This literature boundary concerns the Jacobian of an actual completed double
cover, with an integral monic equation and separable reduction. It includes
neither a Galois representation nor a manuscript-specific comparison.
-/

public noncomputable section

open CategoryTheory Polynomial
open scoped NumberField CategoryTheory.MonObj

namespace AlgebraicGeometry.GroupScheme

attribute [local instance] Ideal.Quotient.field

/-- A pointed isomorphism of curves preserves the same Jacobian and carries
its Abel–Jacobi map by composition. -/
def PointedCurveJacobian.transport
    {K : Type*} [Field K]
    {C D : Over (Spec (CommRingCat.of K))}
    {b : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ C}
    {J : CommGrp (Over (Spec (CommRingCat.of K)))}
    (hJ : PointedCurveJacobian K C b J) (e : D ≅ C) :
    PointedCurveJacobian K D (b ≫ e.inv) J where
  targetProper := hJ.targetProper
  targetSmooth := hJ.targetSmooth
  targetGeometricallyConnected := hJ.targetGeometricallyConnected
  abelJacobi := e.hom ≫ hJ.abelJacobi
  normalized := by
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hJ.normalized
  universal := by
    intro A hproper hsmooth hconn f hnorm
    have hnorm' : b ≫ (e.inv ≫ f) =
        (1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X) := by
      simpa only [Category.assoc] using hnorm
    obtain ⟨h, hh, hu⟩ := hJ.universal A hproper hsmooth hconn (e.inv ≫ f) hnorm'
    refine ⟨h, ?_, ?_⟩
    · calc
        (e.hom ≫ hJ.abelJacobi) ≫ h.hom.hom.hom =
            e.hom ≫ (hJ.abelJacobi ≫ h.hom.hom.hom) := Category.assoc _ _ _
        _ = e.hom ≫ (e.inv ≫ f) := by rw [hh]
        _ = f := by rw [← Category.assoc, e.hom_inv_id, Category.id_comp]
    · intro h' hh'
      apply hu
      calc
        hJ.abelJacobi ≫ h'.hom.hom.hom =
            e.inv ≫ ((e.hom ≫ hJ.abelJacobi) ≫ h'.hom.hom.hom) := by
              simp only [Category.assoc, ← Category.assoc e.inv e.hom,
                e.inv_hom_id, Category.id_comp]
        _ = e.inv ≫ f := by rw [hh']

/-- Monicity keeps the degree of the actual branch polynomial after reduction. -/
theorem hyperellipticReducedPolynomial_degree
    (K : Type*) [Field K] [NumberField K]
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (n : ℕ) (f₀ : (P.valuationSubringAtPrime K)[X])
    (hmonic : f₀.Monic) (hdegree : f₀.natDegree = 2 * n) :
    (f₀.map (P.localResidue (K := K))).natDegree = 2 * n :=
  (hmonic.natDegree_map (P.localResidue (K := K))).trans hdegree

/-- The relative Jacobian of the actual smooth two-chart double cover has
the supplied pointed Jacobian as generic fibre and the pointed Jacobian of
the *reduced equation* as special fibre. The special point and Abel–Jacobi
map are the fields of the returned `PointedCurveJacobian`; the generic
identification and the special Jacobian belong to the same model `B`.

This is the standard relative Picard/Jacobian and base-change result
[MilneJacobian2021, Proposition 6.1, printed p.19; Theorem 8.1 and paragraph
following it, printed pp.27–28; Corollary 12.3 and proof, printed p.39],
applied to the monic two-chart hyperelliptic model with separable residue
polynomial [src_poonen_curves, §2.8.1, printed pp.36–37]. It is a standard
composite interface, not a numeric Frobenius or RM assertion. -/
theorem exists_hyperellipticJacobian_goodReduction_withSpecialFiber
    (K : Type*) [Field K] [NumberField K]
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (n : ℕ) (hn : 0 < n)
    (f : K[X]) (hf : f.natDegree = 2 * n)
    (f₀ : (P.valuationSubringAtPrime K)[X]) (hmonic : f₀.Monic)
    (hdegree : f₀.natDegree = 2 * n)
    (hgeneric : f₀.map (algebraMap (P.valuationSubringAtPrime K) K) = f)
    (h2 : (2 : 𝓞 K) ∉ P.asIdeal)
    (hsep : (f₀.map (P.localResidue (K := K))).Separable)
    (b : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      Over.mk (Hyperelliptic.toSpec f n hf))
    (J : CommGrp (Over (Spec (CommRingCat.of K))))
    (hJ : PointedCurveJacobian K (Over.mk (Hyperelliptic.toSpec f n hf)) b J) :
    let fₛ := f₀.map (P.localResidue (K := K))
    let hdegreeₛ : fₛ.natDegree = 2 * n :=
      hyperellipticReducedPolynomial_degree K P n f₀ hmonic hdegree
    ∃ (B : CommGrp (Over (Spec (CommRingCat.of (P.valuationSubringAtPrime K))))),
      IsProper B.X.hom ∧ Smooth B.X.hom ∧ GeometricallyConnected B.X.hom ∧
        Nonempty (J ≅ localGenericFiber K P B) ∧
        ∃ bₛ : Over.mk (𝟙 (Spec (CommRingCat.of (𝓞 K ⧸ P.asIdeal)))) ⟶
          Over.mk (Hyperelliptic.toSpec fₛ n hdegreeₛ),
          Nonempty (PointedCurveJacobian (𝓞 K ⧸ P.asIdeal)
            (Over.mk (Hyperelliptic.toSpec fₛ n hdegreeₛ)) bₛ
            (localSpecialFiber K P B)) := by
  sorry

/-- A monic even-degree hyperelliptic equation with separable reduction away
from two gives good reduction of its pointed Jacobian.

This is a standard combined consequence of the smooth discriminant criterion
for a double cover (the criterion used in [DarmonRigid, Proposition 1.15,
proof, printed p. 426]) and [MilneJacobian2021, Theorem 8.1 and the following
paragraph, pp. 27–28; Corollary 12.3, proof, p. 39]. The two integral charts
are `y² = f₀(x)` and its reciprocal chart. Monicity retains the degree; the
unit `2` and separable reduction make both fibres smooth and geometrically
integral. They give a projective smooth curve over the displayed DVR.
Its relative Jacobian is an abelian scheme and commutes with generic base
change. [MilneJacobian2021, Proposition 6.1, p. 19] identifies that generic
Jacobian with the supplied pointed universal target `J`. The supplied rational
point extends over the DVR by properness. This is not a verbatim single source
theorem. It imposes the full local equation hypotheses rather than asserting
good reduction for an arbitrary family. -/
theorem exists_hyperellipticJacobian_goodReduction_of_separable
    (K : Type*) [Field K] [NumberField K]
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (n : ℕ) (hn : 0 < n)
    (f : K[X]) (hf : f.natDegree = 2 * n)
    (f₀ : (P.valuationSubringAtPrime K)[X]) (hmonic : f₀.Monic)
    (hdegree : f₀.natDegree = 2 * n)
    (hgeneric : f₀.map (algebraMap (P.valuationSubringAtPrime K) K) = f)
    (h2 : (2 : 𝓞 K) ∉ P.asIdeal)
    (hsep : (f₀.map (P.localResidue (K := K))).Separable)
    (b : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      Over.mk (Hyperelliptic.toSpec f n hf))
    (J : CommGrp (Over (Spec (CommRingCat.of K))))
    (hJ : PointedCurveJacobian K (Over.mk (Hyperelliptic.toSpec f n hf)) b J) :
    ∃ (B : CommGrp (Over (Spec (CommRingCat.of (P.valuationSubringAtPrime K))))),
      IsProper B.X.hom ∧ Smooth B.X.hom ∧ GeometricallyConnected B.X.hom ∧
        Nonempty (J ≅ localGenericFiber K P B) := by
  -- Preserve the original interface by projecting the one richer literature witness.
  obtain ⟨B, hproper, hsmooth, hconnected, he, _⟩ :=
    exists_hyperellipticJacobian_goodReduction_withSpecialFiber
      K P n hn f hf f₀ hmonic hdegree hgeneric h2 hsep b J hJ
  exact ⟨B, hproper, hsmooth, hconnected, he⟩

end AlgebraicGeometry.GroupScheme
