/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hyperelliptic.SpecialFiberTensor
public import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Affine fibres of the scaled double cover

The residue quadratic charts are actual scheme-theoretic pullbacks of the family
charts. These identifications retain both the polynomial-base projection and the
map to the original quadratic chart. The global glued fibre requires a separate
overlap argument.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
open scoped TensorProduct

namespace HilbertModularity.Hyperelliptic

universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

local instance : Algebra R[X] S[X] :=
  (Polynomial.mapRingHom (algebraMap R S)).toAlgebra

/-- The finite affine chart of the reduced cover is the pullback of the finite
family chart over the coefficient-changed affine line. -/
def finiteSpecializationChartPullbackIso (P : R[X]) (t : R)
    (ht : algebraMap R S t = 0) :
    Spec (CommRingCat.of
      (AlgebraicGeometry.DoubleCover.ChartRing
        (finiteBranchPolynomial (P.map (algebraMap R S)) 0))) ≅
      pullback (Spec.map (CommRingCat.ofHom (algebraMap R[X] S[X])))
        (Spec.map (CommRingCat.ofHom
          (algebraMap R[X]
            (AlgebraicGeometry.DoubleCover.ChartRing (finiteBranchPolynomial P t))))) :=
  Scheme.Spec.mapIso
      (finiteSpecializationTensorEquiv (S := S) P t ht).toRingEquiv.toCommRingCatIso.op ≪≫
    (pullbackSpecIso R[X] S[X]
      (AlgebraicGeometry.DoubleCover.ChartRing (finiteBranchPolynomial P t))).symm

/-- The reciprocal affine chart of the reduced cover is the corresponding
pullback. Monicity preserves the projective transition exponent. -/
def infinitySpecializationChartPullbackIso [Nontrivial S] (P : R[X]) (t : R)
    (ht : algebraMap R S t = 0) (hP : P.Monic) :
    Spec (CommRingCat.of
      (AlgebraicGeometry.DoubleCover.ChartRing
        (infinityBranchPolynomial (P.map (algebraMap R S)) 0))) ≅
      pullback (Spec.map (CommRingCat.ofHom (algebraMap R[X] S[X])))
        (Spec.map (CommRingCat.ofHom
          (algebraMap R[X]
            (AlgebraicGeometry.DoubleCover.ChartRing (infinityBranchPolynomial P t))))) :=
  Scheme.Spec.mapIso
      (infinitySpecializationTensorEquiv (S := S) P t ht hP).toRingEquiv.toCommRingCatIso.op ≪≫
    (pullbackSpecIso R[X] S[X]
      (AlgebraicGeometry.DoubleCover.ChartRing (infinityBranchPolynomial P t))).symm

/-- The finite pullback's first projection is the polynomial-base structure map. -/
theorem finiteSpecializationChartPullbackIso_fst (P : R[X]) (t : R)
    (ht : algebraMap R S t = 0) :
    (finiteSpecializationChartPullbackIso (S := S) P t ht).hom ≫
        pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R[X] S[X])))
          (Spec.map (CommRingCat.ofHom
            (algebraMap R[X]
              (AlgebraicGeometry.DoubleCover.ChartRing (finiteBranchPolynomial P t))))) =
      Spec.map (CommRingCat.ofHom
        (algebraMap S[X]
          (AlgebraicGeometry.DoubleCover.ChartRing
            (finiteBranchPolynomial (P.map (algebraMap R S)) 0)))) := by
  change Spec.map (CommRingCat.ofHom
      (finiteSpecializationTensorEquiv (S := S) P t ht).toRingHom) ≫
      (pullbackSpecIso R[X] S[X]
        (AlgebraicGeometry.DoubleCover.ChartRing (finiteBranchPolynomial P t))).inv ≫
        pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R[X] S[X])))
          (Spec.map (CommRingCat.ofHom
            (algebraMap R[X]
              (AlgebraicGeometry.DoubleCover.ChartRing (finiteBranchPolynomial P t))))) = _
  rw [pullbackSpecIso_inv_fst', ← Spec.map_comp]
  congr 1
  rw [← CommRingCat.ofHom_comp]
  congr 1
  apply RingHom.ext
  intro s
  exact (finiteSpecializationTensorEquiv (S := S) P t ht).commutes s

/-- The finite pullback's second projection is the actual chart specialization. -/
theorem finiteSpecializationChartPullbackIso_snd (P : R[X]) (t : R)
    (ht : algebraMap R S t = 0) :
    (finiteSpecializationChartPullbackIso (S := S) P t ht).hom ≫
        pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R[X] S[X])))
          (Spec.map (CommRingCat.ofHom
            (algebraMap R[X]
              (AlgebraicGeometry.DoubleCover.ChartRing (finiteBranchPolynomial P t))))) =
      Spec.map (CommRingCat.ofHom
        (finiteSpecializationMap (algebraMap R S) P t ht)) := by
  change Spec.map (CommRingCat.ofHom
      (finiteSpecializationTensorEquiv (S := S) P t ht).toRingHom) ≫
      (pullbackSpecIso R[X] S[X]
        (AlgebraicGeometry.DoubleCover.ChartRing (finiteBranchPolynomial P t))).inv ≫
        pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R[X] S[X])))
          (Spec.map (CommRingCat.ofHom
            (algebraMap R[X]
              (AlgebraicGeometry.DoubleCover.ChartRing (finiteBranchPolynomial P t))))) = _
  rw [pullbackSpecIso_inv_snd, ← Spec.map_comp]
  congr 1
  rw [← CommRingCat.ofHom_comp]
  congr 1
  apply RingHom.ext
  intro z
  exact finiteSpecializationTensorEquiv_includeRight (S := S) P t ht z

/-- The reciprocal pullback's first projection is the polynomial-base structure map. -/
theorem infinitySpecializationChartPullbackIso_fst [Nontrivial S] (P : R[X]) (t : R)
    (ht : algebraMap R S t = 0) (hP : P.Monic) :
    (infinitySpecializationChartPullbackIso (S := S) P t ht hP).hom ≫
        pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R[X] S[X])))
          (Spec.map (CommRingCat.ofHom
            (algebraMap R[X]
              (AlgebraicGeometry.DoubleCover.ChartRing (infinityBranchPolynomial P t))))) =
      Spec.map (CommRingCat.ofHom
        (algebraMap S[X]
          (AlgebraicGeometry.DoubleCover.ChartRing
            (infinityBranchPolynomial (P.map (algebraMap R S)) 0)))) := by
  change Spec.map (CommRingCat.ofHom
      (infinitySpecializationTensorEquiv (S := S) P t ht hP).toRingHom) ≫
      (pullbackSpecIso R[X] S[X]
        (AlgebraicGeometry.DoubleCover.ChartRing (infinityBranchPolynomial P t))).inv ≫
        pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R[X] S[X])))
          (Spec.map (CommRingCat.ofHom
            (algebraMap R[X]
              (AlgebraicGeometry.DoubleCover.ChartRing (infinityBranchPolynomial P t))))) = _
  rw [pullbackSpecIso_inv_fst', ← Spec.map_comp]
  congr 1
  rw [← CommRingCat.ofHom_comp]
  congr 1
  apply RingHom.ext
  intro s
  exact (infinitySpecializationTensorEquiv (S := S) P t ht hP).commutes s

/-- The reciprocal pullback's second projection is the actual chart specialization. -/
theorem infinitySpecializationChartPullbackIso_snd [Nontrivial S] (P : R[X]) (t : R)
    (ht : algebraMap R S t = 0) (hP : P.Monic) :
    (infinitySpecializationChartPullbackIso (S := S) P t ht hP).hom ≫
        pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R[X] S[X])))
          (Spec.map (CommRingCat.ofHom
            (algebraMap R[X]
              (AlgebraicGeometry.DoubleCover.ChartRing (infinityBranchPolynomial P t))))) =
      Spec.map (CommRingCat.ofHom
        (infinitySpecializationMap (algebraMap R S) P t ht hP)) := by
  change Spec.map (CommRingCat.ofHom
      (infinitySpecializationTensorEquiv (S := S) P t ht hP).toRingHom) ≫
      (pullbackSpecIso R[X] S[X]
        (AlgebraicGeometry.DoubleCover.ChartRing (infinityBranchPolynomial P t))).inv ≫
        pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R[X] S[X])))
          (Spec.map (CommRingCat.ofHom
            (algebraMap R[X]
              (AlgebraicGeometry.DoubleCover.ChartRing (infinityBranchPolynomial P t))))) = _
  rw [pullbackSpecIso_inv_snd, ← Spec.map_comp]
  congr 1
  rw [← CommRingCat.ofHom_comp]
  congr 1
  apply RingHom.ext
  intro z
  exact infinitySpecializationTensorEquiv_includeRight (S := S) P t ht hP z

/-- The actual finite quadratic chart is the scheme-theoretic coefficient fibre
of the finite chart in the family. -/
theorem finiteSpecializationChart_isPullback (P : R[X]) (t : R)
    (ht : algebraMap R S t = 0) :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (algebraMap S[X]
          (AlgebraicGeometry.DoubleCover.ChartRing
            (finiteBranchPolynomial (P.map (algebraMap R S)) 0)))))
      (Spec.map (CommRingCat.ofHom
        (finiteSpecializationMap (algebraMap R S) P t ht)))
      (Spec.map (CommRingCat.ofHom (algebraMap R[X] S[X])))
      (Spec.map (CommRingCat.ofHom
        (algebraMap R[X]
          (AlgebraicGeometry.DoubleCover.ChartRing (finiteBranchPolynomial P t))))) := by
  let e := finiteSpecializationChartPullbackIso (S := S) P t ht
  have h₁ := finiteSpecializationChartPullbackIso_fst (S := S) P t ht
  have h₂ := finiteSpecializationChartPullbackIso_snd (S := S) P t ht
  apply IsPullback.of_iso_pullback
    (show CommSq _ _ _ _ from ⟨by
      calc
        _ = (e.hom ≫ pullback.fst _ _) ≫ _ := by rw [h₁]
        _ = (e.hom ≫ pullback.snd _ _) ≫ _ := by rw [Category.assoc, pullback.condition, ← Category.assoc]
        _ = _ := by rw [h₂]⟩)
    e h₁ h₂

/-- The reciprocal quadratic chart is likewise the scheme-theoretic coefficient
fibre; monicity keeps the projective transition exponent fixed. -/
theorem infinitySpecializationChart_isPullback [Nontrivial S] (P : R[X]) (t : R)
    (ht : algebraMap R S t = 0) (hP : P.Monic) :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (algebraMap S[X]
          (AlgebraicGeometry.DoubleCover.ChartRing
            (infinityBranchPolynomial (P.map (algebraMap R S)) 0)))))
      (Spec.map (CommRingCat.ofHom
        (infinitySpecializationMap (algebraMap R S) P t ht hP)))
      (Spec.map (CommRingCat.ofHom (algebraMap R[X] S[X])))
      (Spec.map (CommRingCat.ofHom
        (algebraMap R[X]
          (AlgebraicGeometry.DoubleCover.ChartRing (infinityBranchPolynomial P t))))) := by
  let e := infinitySpecializationChartPullbackIso (S := S) P t ht hP
  have h₁ := infinitySpecializationChartPullbackIso_fst (S := S) P t ht hP
  have h₂ := infinitySpecializationChartPullbackIso_snd (S := S) P t ht hP
  apply IsPullback.of_iso_pullback
    (show CommSq _ _ _ _ from ⟨by
      calc
        _ = (e.hom ≫ pullback.fst _ _) ≫ _ := by rw [h₁]
        _ = (e.hom ≫ pullback.snd _ _) ≫ _ := by rw [Category.assoc, pullback.condition, ← Category.assoc]
        _ = _ := by rw [h₂]⟩)
    e h₁ h₂

end HilbertModularity.Hyperelliptic
