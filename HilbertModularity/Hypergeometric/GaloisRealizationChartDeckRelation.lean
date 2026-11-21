/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.GaloisRealizationChartScheme

/-! # Reflection and deck transformations on the Euler chart

The geometric reflection of [GPRV, Proposition 9.5, equation (76)] conjugates
the actual deck transformation to its inverse.  These statements identify the
maps on the coordinate ring and affine scheme, before passing to a proper
fibre or its cohomology.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial

namespace HilbertModularity.Hypergeometric.EulerCover

variable {K : Type*} [Field K]

/-- The function-field reflection conjugates the actual deck transformation
to inverse deck scaling.  Both maps are extensions of the original affine
Euler coordinate-ring automorphisms. -/
theorem genericReflectionFunctionFieldHom_comp_deck (N m : ℕ) [NeZero N]
    (t : K) (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N)
    (ht : t ≠ 0) (ζ : rootsOfUnity N K) :
    letI := coverRing_isDomain N m t (NeZero.ne N) hmPos hm hcop
    (genericReflectionFunctionFieldHom N m t (NeZero.ne N) hmPos hm hcop ht).comp
        (deckFunctionFieldAction N m t ζ).toRingHom =
      (deckFunctionFieldAction N m t ζ⁻¹).toRingHom.comp
        (genericReflectionFunctionFieldHom N m t (NeZero.ne N) hmPos hm hcop ht) := by
  let : IsDomain (CoverRing N m t) :=
    coverRing_isDomain N m t (NeZero.ne N) hmPos hm hcop
  let r := genericReflectionFunctionFieldHom N m t (NeZero.ne N) hmPos hm hcop ht
  let d := deckFunctionFieldAction N m t ζ
  let di := deckFunctionFieldAction N m t ζ⁻¹
  let x := coverFunctionFieldX N m t
  let y := coverFunctionFieldRoot N m t
  let τ := algebraMap K (CoverFunctionField N m t) t
  let z := algebraMap K (CoverFunctionField N m t) ((ζ : Kˣ) : K)
  have hc (a : K) :
      algebraMap K[X] (CoverFunctionField N m t) (C a) =
        algebraMap K (CoverFunctionField N m t) a := by
    rw [← Polynomial.algebraMap_eq]
    exact (IsScalarTower.algebraMap_apply K K[X]
      (CoverFunctionField N m t) a).symm
  have hrconst (a : K) : r (algebraMap K (CoverFunctionField N m t) a) =
      algebraMap K (CoverFunctionField N m t) a :=
    genericReflectionFunctionFieldHom_const N m t (NeZero.ne N) hmPos hm hcop ht a
  have hrx : r x = reflectionX τ x :=
    genericReflectionFunctionFieldHom_x N m t (NeZero.ne N) hmPos hm hcop ht
  have hry : r y = reflectionY τ x y :=
    genericReflectionFunctionFieldHom_root N m t (NeZero.ne N) hmPos hm hcop ht
  have hdx : d x = x := deckFunctionFieldAction_X N m t hmPos hm hcop ζ
  have hdix : di x = x := deckFunctionFieldAction_X N m t hmPos hm hcop ζ⁻¹
  have hdconst (a : K) : d (algebraMap K (CoverFunctionField N m t) a) =
      algebraMap K (CoverFunctionField N m t) a := by
    exact d.commutes (algebraMap K (BaseRing t) a)
  have hdiconst (a : K) : di (algebraMap K (CoverFunctionField N m t) a) =
      algebraMap K (CoverFunctionField N m t) a := by
    exact di.commutes (algebraMap K (BaseRing t) a)
  have hdy : d y = z * y := by
    simpa only [y, z, Algebra.smul_def,
      ← IsScalarTower.algebraMap_apply K[X] (BaseRing t)
        (CoverFunctionField N m t), hc] using
      deckFunctionFieldAction_root N m t ζ
  have hdiy : di y = z⁻¹ * y := by
    have h := deckFunctionFieldAction_root N m t ζ⁻¹
    have hζ : (((ζ⁻¹ : rootsOfUnity N K) : Kˣ) : K) =
        (((ζ : Kˣ) : K))⁻¹ := by
      change (((ζ : Kˣ)⁻¹ : Kˣ) : K) = (((ζ : Kˣ) : K))⁻¹
      exact Units.val_inv_eq_inv_val (ζ : Kˣ)
    have h' : di y =
        algebraMap K (CoverFunctionField N m t)
          (((ζ⁻¹ : rootsOfUnity N K) : Kˣ) : K) * y := by
      simpa only [y, Algebra.smul_def,
      ← IsScalarTower.algebraMap_apply K[X] (BaseRing t)
        (CoverFunctionField N m t), hc] using h
    rw [hζ] at h'
    simpa only [z, map_inv₀] using h'
  have hz : z ≠ 0 := by
    exact (map_ne_zero (algebraMap K (CoverFunctionField N m t))).mpr (Units.ne_zero _)
  have hdiτ : di.toRingHom τ = τ := by
    change di τ = τ
    exact hdiconst t
  have hdix' : di.toRingHom x = x := by
    change di x = x
    exact hdix
  have hdiy' : di.toRingHom y = z⁻¹ * y := by
    change di y = z⁻¹ * y
    exact hdiy
  have hroot : r (d y) = di (r y) := by
    rw [hdy, map_mul, hrconst, hry]
    change z * reflectionY τ x y = di.toRingHom (reflectionY τ x y)
    rw [map_reflectionY di.toRingHom, hdiτ, hdix', hdiy']
    simpa only [inv_inv] using (reflectionY_deck (t := τ) (x := x) (y := y)
      (ζ := z⁻¹) (inv_ne_zero hz)).symm
  have hxrel : r (d x) = di (r x) := by
    rw [hdx, hrx]
    change reflectionX τ x = di.toRingHom (reflectionX τ x)
    rw [map_reflectionX di.toRingHom, hdiτ, hdix']
  apply IsFractionRing.ringHom_ext (A := CoverRing N m t)
  intro a
  have hcomp : (r.comp d.toRingHom).comp
      (algebraMap (CoverRing N m t) (CoverFunctionField N m t)) =
      (di.toRingHom.comp r).comp
        (algebraMap (CoverRing N m t) (CoverFunctionField N m t)) := by
    apply AdjoinRoot.ringHom_ext
    · apply IsLocalization.ringHom_ext (Submonoid.powers (branchProduct t))
      apply Polynomial.ringHom_ext
      · intro c
        change r (d (algebraMap K (CoverFunctionField N m t) c)) =
          di (r (algebraMap K (CoverFunctionField N m t) c))
        rw [hdconst, hrconst, hdiconst]
      · change r (d x) = di (r x)
        exact hxrel
    · change r (d y) = di (r y)
      exact hroot
  exact congrArg (fun f : CoverRing N m t →+* CoverFunctionField N m t => f a) hcomp

/-- The affine coordinate-ring reflection conjugates the actual deck action
to inverse deck scaling, with the same root-of-unity label. -/
theorem reflectionChartCoverHom_comp_deck (N m : ℕ) [NeZero N]
    (t : K) (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N)
    (ht : t ≠ 0) (ζ : rootsOfUnity N K) :
    (reflectionChartCoverHom N m t (NeZero.ne N) hmPos hm hcop ht).comp
        (deckAlgebraAction N m t ζ).toRingHom =
      (deckAlgebraAction N m t ζ⁻¹).toRingHom.comp
        (reflectionChartCoverHom N m t (NeZero.ne N) hmPos hm hcop ht) := by
  let : IsDomain (CoverRing N m t) :=
    coverRing_isDomain N m t (NeZero.ne N) hmPos hm hcop
  let j := algebraMap (CoverRing N m t) (CoverFunctionField N m t)
  let r := reflectionChartCoverHom N m t (NeZero.ne N) hmPos hm hcop ht
  let d := deckAlgebraAction N m t ζ
  let di := deckAlgebraAction N m t ζ⁻¹
  apply RingHom.ext
  intro a
  apply IsFractionRing.injective (CoverRing N m t) (CoverFunctionField N m t)
  have hr (b : CoverRing N m t) : j (r b) =
      genericReflectionFunctionFieldHom N m t (NeZero.ne N) hmPos hm hcop ht
        (j b) := by
    have h := congrArg (fun f : CoverRing N m t →+* CoverFunctionField N m t => f b)
      (reflectionChartCoverHom_toFunctionField N m t (NeZero.ne N)
        hmPos hm hcop ht)
    simpa only [j, r, RingHom.comp_apply] using h
  have hd (b : CoverRing N m t) : j (d b) =
      deckFunctionFieldAction N m t ζ (j b) := by
    exact (IsFractionRing.algEquivOfAlgEquiv_algebraMap d b).symm
  have hdi (b : CoverRing N m t) : j (di b) =
      deckFunctionFieldAction N m t ζ⁻¹ (j b) := by
    exact (IsFractionRing.algEquivOfAlgEquiv_algebraMap di b).symm
  change j (r (d a)) = j (di (r a))
  rw [hr, hd, hdi, hr]
  exact congrArg (fun f : CoverFunctionField N m t →+* CoverFunctionField N m t =>
    f (j a)) (genericReflectionFunctionFieldHom_comp_deck N m t hmPos hm hcop ht ζ)

/-- The same conjugation relation for the actual affine Euler scheme maps. -/
theorem reflectionChartSchemeIso_comp_deck (N m : ℕ) [NeZero N]
    (t : K) (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N)
    (ht : t ≠ 0) (ζ : rootsOfUnity N K) :
    (reflectionChartSchemeIso N m t (NeZero.ne N) hmPos hm hcop ht).hom ≫
        (deckTransformation N m t ζ).hom =
      (deckTransformation N m t ζ⁻¹).hom ≫
        (reflectionChartSchemeIso N m t (NeZero.ne N) hmPos hm hcop ht).hom := by
  simp only [reflectionChartSchemeIso_hom, deckTransformation_hom]
  erw [← Spec.map_comp, ← Spec.map_comp]
  rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 1
  exact congrArg CommRingCat.ofHom
    (reflectionChartCoverHom_comp_deck N m t hmPos hm hcop ht ζ)

end HilbertModularity.Hypergeometric.EulerCover
