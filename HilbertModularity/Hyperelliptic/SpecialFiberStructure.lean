/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hyperelliptic.SpecialFiberSchemeFibre

/-! # Structure map of the specialized scaled cover

The coefficient specialization of the glued cover respects its structure map
to the coefficient spectrum. This is checked on its two quadratic chart opens.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial

namespace HilbertModularity.Hyperelliptic

universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Nontrivial S]

/-- The structure map of the scaled projective double cover. -/
abbrev scaledDoubleCoverToSpec (P : R[X]) (t : R) :
    scaledDoubleCover P t ⟶ Spec (CommRingCat.of R) :=
  scaledDoubleCoverProjection P t ≫ ProjectiveLine.toSpec R

omit [Nontrivial S] in
/-- Coefficient change on the finite quadratic chart respects the base ring. -/
theorem finiteChartMap_coeff (f : R →+* S) (P : R[X]) (t : R) :
    (finiteChartMap f P t).comp
        (algebraMap R (DoubleCover.ChartRing (finiteBranchPolynomial P t))) =
      (algebraMap S (DoubleCover.ChartRing
        (finiteBranchPolynomial (P.map f) (f t)))).comp f := by
  apply RingHom.ext
  intro r
  apply QuadraticAlgebra.ext
  · simp
  · simp

omit [Nontrivial S] in
/-- Coefficient change on the reciprocal quadratic chart respects the base ring. -/
theorem infinityChartMap_coeff (f : R →+* S) (P : R[X]) (t : R)
    (hdeg : (P.map f).natDegree = P.natDegree) :
    (infinityChartMap f P t hdeg).comp
        (algebraMap R (DoubleCover.ChartRing (infinityBranchPolynomial P t))) =
      (algebraMap S (DoubleCover.ChartRing
        (infinityBranchPolynomial (P.map f) (f t)))).comp f := by
  apply RingHom.ext
  intro r
  apply QuadraticAlgebra.ext
  · simp
  · simp

omit [Nontrivial S] in
/-- On the finite chart, coefficient specialization commutes with the map to
the coefficient spectrum. -/
theorem finiteChartMap_toSpec (f : R →+* S) (P : R[X]) (t : R) :
    Spec.map (CommRingCat.ofHom (finiteChartMap f P t)) ≫
        DoubleCover.finiteProjection (finiteBranchPolynomial P t) ≫
        ProjectiveLine.toSpec R =
      DoubleCover.finiteProjection (finiteBranchPolynomial (P.map f) (f t)) ≫
        ProjectiveLine.toSpec S ≫ Spec.map (CommRingCat.ofHom f) := by
  rw [DoubleCover.finiteProjection_toSpec, ← Category.assoc,
    DoubleCover.finiteProjection_toSpec, ← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun g => Spec.map (CommRingCat.ofHom g))
    (finiteChartMap_coeff f P t)

omit [Nontrivial S] in
/-- On the reciprocal chart, coefficient specialization commutes with the map
to the coefficient spectrum. -/
theorem infinityChartMap_toSpec (f : R →+* S) (P : R[X]) (t : R)
    (hdeg : (P.map f).natDegree = P.natDegree) :
    Spec.map (CommRingCat.ofHom (infinityChartMap f P t hdeg)) ≫
        DoubleCover.infinityProjection (infinityBranchPolynomial P t) ≫
        ProjectiveLine.toSpec R =
      DoubleCover.infinityProjection (infinityBranchPolynomial (P.map f) (f t)) ≫
        ProjectiveLine.toSpec S ≫ Spec.map (CommRingCat.ofHom f) := by
  rw [DoubleCover.infinityProjection_toSpec, ← Category.assoc,
    DoubleCover.infinityProjection_toSpec, ← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun g => Spec.map (CommRingCat.ofHom g))
    (infinityChartMap_coeff f P t hdeg)

omit [Nontrivial S] in
/-- Coefficient specialization of the glued scaled cover is a morphism over
the induced map of coefficient spectra. -/
theorem scaledDoubleCoverMap_toSpec (f : R →+* S) (P : R[X]) (t : R)
    (hdeg : (P.map f).natDegree = P.natDegree) :
    scaledDoubleCoverMap f P t hdeg ≫ scaledDoubleCoverToSpec P t =
      scaledDoubleCoverToSpec (P.map f) (f t) ≫
        Spec.map (CommRingCat.ofHom f) := by
  apply (DoubleCover.openCover
    (finiteBranchPolynomial (P.map f) (f t))
    (infinityBranchPolynomial (P.map f) (f t))
    ((P.map f).natDegree + 1) (branch_transition (P.map f) (f t))).hom_ext
  intro b
  cases b
  · have hchart := congrArg
        (fun q => q ≫ scaledDoubleCoverToSpec P t)
        (finiteChart_scaledDoubleCoverMap f P t hdeg)
    have hbase :
        Spec.map (CommRingCat.ofHom (finiteChartMap f P t)) ≫
          DoubleCover.finiteChart
            (finiteBranchPolynomial P t) (infinityBranchPolynomial P t)
            (P.natDegree + 1) (branch_transition P t) ≫
          scaledDoubleCoverToSpec P t =
        DoubleCover.finiteChart
            (finiteBranchPolynomial (P.map f) (f t))
            (infinityBranchPolynomial (P.map f) (f t))
            ((P.map f).natDegree + 1) (branch_transition (P.map f) (f t)) ≫
          scaledDoubleCoverToSpec (P.map f) (f t) ≫
          Spec.map (CommRingCat.ofHom f) := by
      have hleft := congrArg
        (fun q => Spec.map (CommRingCat.ofHom (finiteChartMap f P t)) ≫ q)
        (finiteChart_scaledDoubleCoverProjection_toSpec P t)
      have hright := congrArg
        (fun q => q ≫ Spec.map (CommRingCat.ofHom f))
        (finiteChart_scaledDoubleCoverProjection_toSpec (P.map f) (f t)).symm
      have hmid := finiteChartMap_toSpec f P t
      simp only [scaledDoubleCoverToSpec, Category.assoc] at hleft hright ⊢
      exact hleft.trans (hmid.trans hright)
    simp only [DoubleCover.openCover, Category.assoc] at hchart hbase ⊢
    exact hchart.trans hbase
  · have hchart := congrArg
        (fun q => q ≫ scaledDoubleCoverToSpec P t)
        (infinityChart_scaledDoubleCoverMap f P t hdeg)
    have hbase :
        Spec.map (CommRingCat.ofHom (infinityChartMap f P t hdeg)) ≫
          DoubleCover.infinityChart
            (finiteBranchPolynomial P t) (infinityBranchPolynomial P t)
            (P.natDegree + 1) (branch_transition P t) ≫
          scaledDoubleCoverToSpec P t =
        DoubleCover.infinityChart
            (finiteBranchPolynomial (P.map f) (f t))
            (infinityBranchPolynomial (P.map f) (f t))
            ((P.map f).natDegree + 1) (branch_transition (P.map f) (f t)) ≫
          scaledDoubleCoverToSpec (P.map f) (f t) ≫
          Spec.map (CommRingCat.ofHom f) := by
      have hleft := congrArg
        (fun q => Spec.map (CommRingCat.ofHom (infinityChartMap f P t hdeg)) ≫ q)
        (infinityChart_scaledDoubleCoverProjection_toSpec P t)
      have hright := congrArg
        (fun q => q ≫ Spec.map (CommRingCat.ofHom f))
        (infinityChart_scaledDoubleCoverProjection_toSpec (P.map f) (f t)).symm
      have hmid := infinityChartMap_toSpec f P t hdeg
      simp only [scaledDoubleCoverToSpec, Category.assoc] at hleft hright ⊢
      exact hleft.trans (hmid.trans hright)
    simp only [DoubleCover.openCover, Category.assoc] at hchart hbase ⊢
    exact hchart.trans hbase

end HilbertModularity.Hyperelliptic
