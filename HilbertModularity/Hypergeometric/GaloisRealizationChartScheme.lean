/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.GaloisRealizationChartAutomorphism

/-! # The reflected Euler chart as a scheme automorphism

The coordinate-ring involution gives an automorphism of the actual affine Euler
chart. Its effect on the branch and cover coordinates is the reflection used in
[GPRV, Proposition 9.5]. This is the chart map to compare with the involution
on the smooth proper Euler family.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial

namespace HilbertModularity.Hypergeometric.EulerCover

variable {K : Type*} [Field K]

/-- The scheme automorphism induced by the regular reflection on the branch-open
Euler coordinate ring. -/
def reflectionChartSchemeIso (N m : ℕ) (t : K) (hN : N ≠ 0)
    (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N) (ht : t ≠ 0) :
    affineScheme N m t ≅ affineScheme N m t :=
  Scheme.Spec.mapIso
    (reflectionChartCoverEquiv N m t hN hmPos hm hcop ht).toCommRingCatIso.op

@[simp] theorem reflectionChartSchemeIso_hom (N m : ℕ) (t : K) (hN : N ≠ 0)
    (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N) (ht : t ≠ 0) :
    (reflectionChartSchemeIso N m t hN hmPos hm hcop ht).hom =
      Spec.map (CommRingCat.ofHom
        (reflectionChartCoverHom N m t hN hmPos hm hcop ht)) := by
  change Spec.map (CommRingCat.ofHom
    (reflectionChartCoverEquiv N m t hN hmPos hm hcop ht :
      CoverRing N m t →+* CoverRing N m t)) = _
  rw [reflectionChartCoverEquiv_toRingHom]

/-- The reflected chart is an automorphism over the original coefficient field. -/
theorem reflectionChartSchemeIso_structureMap (N m : ℕ) (t : K) (hN : N ≠ 0)
    (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N) (ht : t ≠ 0) :
    (reflectionChartSchemeIso N m t hN hmPos hm hcop ht).hom ≫
        structureMap N m t = structureMap N m t := by
  rw [reflectionChartSchemeIso_hom, structureMap]
  erw [← Spec.map_comp]
  congr 1
  ext a
  exact reflectionChartCoverHom_const N m t hN hmPos hm hcop ht a

/-- The spectrum automorphism retains the order-two property of its coordinate
ring map. -/
theorem reflectionChartSchemeIso_sq (N m : ℕ) (t : K) (hN : N ≠ 0)
    (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N) (ht : t ≠ 0) :
    reflectionChartSchemeIso N m t hN hmPos hm hcop ht ≪≫
      reflectionChartSchemeIso N m t hN hmPos hm hcop ht =
        Iso.refl (affineScheme N m t) := by
  apply Iso.ext
  change (reflectionChartSchemeIso N m t hN hmPos hm hcop ht).hom ≫
    (reflectionChartSchemeIso N m t hN hmPos hm hcop ht).hom = 𝟙 _
  rw [reflectionChartSchemeIso_hom]
  erw [← Spec.map_comp]
  rw [← CommRingCat.ofHom_comp,
    reflectionChartCoverHom_involutive N m t hN hmPos hm hcop ht]
  exact Spec.map_id _

end HilbertModularity.Hypergeometric.EulerCover
