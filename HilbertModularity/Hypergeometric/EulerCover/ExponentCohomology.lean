/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.EulerCover.ExponentChange
public import HilbertModularity.Hypergeometric.EulerCover.Cohomology
public import HilbertModularity.RepresentationTheory.CharacterProjectorTransport

/-! # Exponent change on affine Euler-cover cohomology

The coprime coordinate change gives an isomorphism of the actual affine
schemes over the coefficient field. We base change that isomorphism to a
geometric field and transport its pro-étale cohomology. The fixed primitive
character on the `m`-cover corresponds to its `m`th power on the base cover;
this is the affine part of [TripathiGoswamiRevised, Definition 2.3].
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Limits
open scoped TensorProduct

namespace HilbertModularity.Hypergeometric.EulerCover

universe u
variable {K : Type u} [Field K] (N m mprime k : ℕ) [NeZero N]
  (t : K) (hm : m < N) (hbezout : m * mprime = 1 + k * N)

/-- Contravariant spectrum of the actual coprime exponent change. Its source
is the base Euler cover, and its target is the `m`-cover. -/
def exponentSchemeIso : affineScheme N 1 t ≅ affineScheme N m t :=
  Scheme.Spec.mapIso
    (exponentChangeEquiv t N m mprime k hm hbezout).toRingEquiv.toCommRingCatIso.op

omit [NeZero N] in
/-- The exponent-change spectrum isomorphism preserves the coefficient-field
structural map. -/
theorem exponentSchemeIso_structureMap :
    (exponentSchemeIso N m mprime k t hm hbezout).hom ≫ structureMap N m t =
      structureMap N 1 t := by
  rw [exponentSchemeIso, structureMap, structureMap]
  erw [← Spec.map_comp]
  congr 1
  ext a
  exact (exponentChangeEquiv t N m mprime k hm hbezout).commutes
    ((algebraMap (Polynomial K) (BaseRing t)) (Polynomial.C a))

/-- On affine schemes, the base deck parameter `ζ` corresponds to `ζ^m` on
the `m`-cover. This is the contravariant spectrum of the algebra identity. -/
theorem exponentSchemeIso_deck (ζ : rootsOfUnity N K) :
    (deckTransformation N 1 t ζ).hom ≫
        (exponentSchemeIso N m mprime k t hm hbezout).hom =
      (exponentSchemeIso N m mprime k t hm hbezout).hom ≫
        (deckTransformation N m t (ζ ^ m)).hom := by
  rw [deckTransformation_hom, deckTransformation_hom]
  change Spec.map (CommRingCat.ofHom (deckAlgebraAction N 1 t ζ).toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (exponentChangeEquiv t N m mprime k hm hbezout).toRingHom) =
    Spec.map (CommRingCat.ofHom
        (exponentChangeEquiv t N m mprime k hm hbezout).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (deckAlgebraAction N m t (ζ ^ m)).toRingHom)
  erw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact congrArg
    (fun φ : CoverRing N m t →ₐ[BaseRing t] CoverRing N 1 t =>
      CommRingCat.ofHom φ.toRingHom)
    (exponentChangeEquiv_deck_baseParameter t N m mprime k hm hbezout ζ).symm

/-- The actual exponent-change isomorphism after geometric base change. -/
def geometricExponentIso :
    geometricAffineScheme N 1 t ≅ geometricAffineScheme N m t := by
  let e := exponentSchemeIso N m mprime k t hm hbezout
  have he : e.hom ≫ structureMap N m t = structureMap N 1 t :=
    exponentSchemeIso_structureMap N m mprime k t hm hbezout
  have hei : e.inv ≫ structureMap N 1 t = structureMap N m t := by
    calc
      e.inv ≫ structureMap N 1 t =
          e.inv ≫ (e.hom ≫ structureMap N m t) := by rw [he]
      _ = (e.inv ≫ e.hom) ≫ structureMap N m t := by rw [Category.assoc]
      _ = structureMap N m t := by simp
  refine
    { hom := pullback.lift (pullback.fst ((GroupScheme.fieldPoint K (AlgebraicClosure K)).hom) (structureMap N 1 t))
        (pullback.snd ((GroupScheme.fieldPoint K (AlgebraicClosure K)).hom) (structureMap N 1 t) ≫ e.hom) ?_
      inv := pullback.lift (pullback.fst ((GroupScheme.fieldPoint K (AlgebraicClosure K)).hom) (structureMap N m t))
        (pullback.snd ((GroupScheme.fieldPoint K (AlgebraicClosure K)).hom) (structureMap N m t) ≫ e.inv) ?_
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · simpa only [Category.assoc, he] using
      (pullback.condition
        (f := (GroupScheme.fieldPoint K (AlgebraicClosure K)).hom)
        (g := structureMap N 1 t))
  · simpa only [Category.assoc, hei] using
      (pullback.condition
        (f := (GroupScheme.fieldPoint K (AlgebraicClosure K)).hom)
        (g := structureMap N m t))
  · apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, Category.id_comp]
    · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
        e.hom_inv_id, Category.comp_id, Category.id_comp]
  · apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, Category.id_comp]
    · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
        e.inv_hom_id, Category.comp_id, Category.id_comp]

omit [NeZero N] in
@[simp] theorem geometricExponentIso_fst :
    (geometricExponentIso N m mprime k t hm hbezout).hom ≫
      pullback.fst ((GroupScheme.fieldPoint K (AlgebraicClosure K)).hom) (structureMap N m t) =
    pullback.fst ((GroupScheme.fieldPoint K (AlgebraicClosure K)).hom) (structureMap N 1 t) := by
  simp only [geometricExponentIso, pullback.lift_fst]

omit [NeZero N] in
@[simp] theorem geometricExponentIso_snd :
    (geometricExponentIso N m mprime k t hm hbezout).hom ≫
      pullback.snd ((GroupScheme.fieldPoint K (AlgebraicClosure K)).hom) (structureMap N m t) =
    pullback.snd ((GroupScheme.fieldPoint K (AlgebraicClosure K)).hom) (structureMap N 1 t) ≫
      (exponentSchemeIso N m mprime k t hm hbezout).hom := by
  simp only [geometricExponentIso, pullback.lift_snd]

/-- The exponent map intertwines actual geometric deck transformations. -/
theorem geometricExponentIso_deck (ζ : rootsOfUnity N K) :
    (geometricDeckIso N 1 t ζ).hom ≫
        (geometricExponentIso N m mprime k t hm hbezout).hom =
      (geometricExponentIso N m mprime k t hm hbezout).hom ≫
        (geometricDeckIso N m t (ζ ^ m)).hom := by
  let e := geometricExponentIso N m mprime k t hm hbezout
  let a := exponentSchemeIso N m mprime k t hm hbezout
  let d₁ := geometricDeckIso N 1 t ζ
  let dₘ := geometricDeckIso N m t (ζ ^ m)
  let p₁ := pullback.snd ((GroupScheme.fieldPoint K (AlgebraicClosure K)).hom)
    (structureMap N 1 t)
  let pₘ := pullback.snd ((GroupScheme.fieldPoint K (AlgebraicClosure K)).hom)
    (structureMap N m t)
  have he : e.hom ≫ pₘ = p₁ ≫ a.hom :=
    geometricExponentIso_snd N m mprime k t hm hbezout
  have hd₁ : d₁.hom ≫ p₁ = p₁ ≫ (deckTransformation N 1 t ζ).hom := by
    simp only [d₁, p₁, geometricDeckIso,
      AlgebraicGeometry.Scheme.baseChangedIso_snd]
  have hdₘ : dₘ.hom ≫ pₘ = pₘ ≫ (deckTransformation N m t (ζ ^ m)).hom := by
    simp only [dₘ, pₘ, geometricDeckIso,
      AlgebraicGeometry.Scheme.baseChangedIso_snd]
  apply pullback.hom_ext
  · simp only [Category.assoc, geometricDeckIso,
      AlgebraicGeometry.Scheme.baseChangedIso_fst,
      geometricExponentIso_fst]
  · change (d₁.hom ≫ e.hom) ≫ pₘ = (e.hom ≫ dₘ.hom) ≫ pₘ
    calc
      (d₁.hom ≫ e.hom) ≫ pₘ = d₁.hom ≫ (p₁ ≫ a.hom) := by
        rw [Category.assoc, he]
      _ = (p₁ ≫ (deckTransformation N 1 t ζ).hom) ≫ a.hom := by
        rw [← Category.assoc, hd₁]
      _ = p₁ ≫ (a.hom ≫ (deckTransformation N m t (ζ ^ m)).hom) := by
        rw [Category.assoc, exponentSchemeIso_deck]
      _ = (e.hom ≫ pₘ) ≫ (deckTransformation N m t (ζ ^ m)).hom := by
        rw [← Category.assoc, ← he]
      _ = e.hom ≫ (dₘ.hom ≫ pₘ) := by
        rw [Category.assoc, hdₘ]
      _ = (e.hom ≫ dₘ.hom) ≫ pₘ := by rw [Category.assoc]

omit [NeZero N] in
/-- Exponent change commutes with the actual ground-field Galois maps on
geometric affine covers. -/
theorem geometricExponentIso_galois
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    (geometricGaloisIso N 1 t σ).hom ≫
        (geometricExponentIso N m mprime k t hm hbezout).hom =
      (geometricExponentIso N m mprime k t hm hbezout).hom ≫
        (geometricGaloisIso N m t σ).hom := by
  let e := geometricExponentIso N m mprime k t hm hbezout
  let a := exponentSchemeIso N m mprime k t hm hbezout
  let g₁ := geometricGaloisIso N 1 t σ
  let gₘ := geometricGaloisIso N m t σ
  let q₁ := pullback.fst ((GroupScheme.fieldPoint K (AlgebraicClosure K)).hom)
    (structureMap N 1 t)
  let qₘ := pullback.fst ((GroupScheme.fieldPoint K (AlgebraicClosure K)).hom)
    (structureMap N m t)
  let p₁ := pullback.snd ((GroupScheme.fieldPoint K (AlgebraicClosure K)).hom)
    (structureMap N 1 t)
  let pₘ := pullback.snd ((GroupScheme.fieldPoint K (AlgebraicClosure K)).hom)
    (structureMap N m t)
  let γ := Spec.map (CommRingCat.ofHom σ.toRingEquiv.toRingHom)
  have heq : e.hom ≫ qₘ = q₁ := geometricExponentIso_fst N m mprime k t hm hbezout
  have hep : e.hom ≫ pₘ = p₁ ≫ a.hom :=
    geometricExponentIso_snd N m mprime k t hm hbezout
  have hgq₁ : g₁.hom ≫ q₁ = q₁ ≫ γ := by
    simp only [g₁, q₁, γ, geometricGaloisIso,
      AlgebraicGeometry.Scheme.fieldBaseChangeGaloisAut_fst]
    rfl
  have hgqₘ : gₘ.hom ≫ qₘ = qₘ ≫ γ := by
    simp only [gₘ, qₘ, γ, geometricGaloisIso,
      AlgebraicGeometry.Scheme.fieldBaseChangeGaloisAut_fst]
    rfl
  have hgp₁ : g₁.hom ≫ p₁ = p₁ := by
    simp only [g₁, p₁, geometricGaloisIso,
      AlgebraicGeometry.Scheme.fieldBaseChangeGaloisAut_snd]
  have hgpₘ : gₘ.hom ≫ pₘ = pₘ := by
    simp only [gₘ, pₘ, geometricGaloisIso,
      AlgebraicGeometry.Scheme.fieldBaseChangeGaloisAut_snd]
  apply pullback.hom_ext
  · change (g₁.hom ≫ e.hom) ≫ qₘ = (e.hom ≫ gₘ.hom) ≫ qₘ
    rw [Category.assoc, heq, hgq₁]
    rw [Category.assoc, hgqₘ]
    calc
      q₁ ≫ γ = (e.hom ≫ qₘ) ≫ γ := by rw [heq]
      _ = e.hom ≫ qₘ ≫ γ := Category.assoc _ _ _
  · change (g₁.hom ≫ e.hom) ≫ pₘ = (e.hom ≫ gₘ.hom) ≫ pₘ
    calc
      (g₁.hom ≫ e.hom) ≫ pₘ = g₁.hom ≫ (p₁ ≫ a.hom) := by
        rw [Category.assoc, hep]
      _ = (g₁.hom ≫ p₁) ≫ a.hom := by rw [Category.assoc]
      _ = p₁ ≫ a.hom := by rw [hgp₁]
      _ = e.hom ≫ pₘ := hep.symm
      _ = e.hom ≫ (gₘ.hom ≫ pₘ) := by rw [hgpₘ]
      _ = (e.hom ≫ gₘ.hom) ≫ pₘ := by rw [Category.assoc]

variable (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ)

/-- Pullback along the actual geometric exponent-change isomorphism on
integral pro-étale cohomology. -/
def geometricExponentIntegralEquiv :
    (geometricAffineScheme N m t).EllAdicCohomology ℓ n ≃ₗ[ℤ_[ℓ]]
      (geometricAffineScheme N 1 t).EllAdicCohomology ℓ n :=
  AlgebraicGeometry.Scheme.ellAdicCohomologyLinearEquiv
    (geometricExponentIso N m mprime k t hm hbezout) ℓ n

/-- Deck pullback intertwines with geometric exponent change. The base deck
parameter acts on the `m`-cover through its `m`th power. -/
theorem geometricExponentIntegralEquiv_deck (ζ : rootsOfUnity N K) :
    (geometricDeckCohomologyRepresentation N 1 t ℓ n ζ).comp
        (geometricExponentIntegralEquiv N m mprime k t hm hbezout ℓ n).toLinearMap =
      (geometricExponentIntegralEquiv N m mprime k t hm hbezout ℓ n).toLinearMap.comp
        (geometricDeckCohomologyRepresentation N m t ℓ n (ζ ^ m)) := by
  let e := geometricExponentIso N m mprime k t hm hbezout
  let d1 := geometricDeckIso N 1 t ζ
  let dm := geometricDeckIso N m t (ζ ^ m)
  have h : d1 ≪≫ e = e ≪≫ dm := by
    apply Iso.ext
    exact geometricExponentIso_deck N m mprime k t hm hbezout ζ
  ext x
  calc
    AlgebraicGeometry.Scheme.ellAdicCohomologyEquiv d1 ℓ n
        (AlgebraicGeometry.Scheme.ellAdicCohomologyEquiv e ℓ n x) =
      AlgebraicGeometry.Scheme.ellAdicCohomologyEquiv (d1 ≪≫ e) ℓ n x :=
        (AlgebraicGeometry.Scheme.ellAdicCohomologyEquiv_trans ℓ d1 e n x).symm
    _ = AlgebraicGeometry.Scheme.ellAdicCohomologyEquiv (e ≪≫ dm) ℓ n x := by rw [h]
    _ = AlgebraicGeometry.Scheme.ellAdicCohomologyEquiv e ℓ n
        (AlgebraicGeometry.Scheme.ellAdicCohomologyEquiv dm ℓ n x) :=
          AlgebraicGeometry.Scheme.ellAdicCohomologyEquiv_trans ℓ e dm n x

omit [NeZero N] in
/-- Geometric exponent change is Galois equivariant over the ground field. -/
theorem geometricExponentIntegralEquiv_galois
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    (geometricGaloisCohomologyRepresentation N 1 t ℓ n σ).comp
        (geometricExponentIntegralEquiv N m mprime k t hm hbezout ℓ n).toLinearMap =
      (geometricExponentIntegralEquiv N m mprime k t hm hbezout ℓ n).toLinearMap.comp
        (geometricGaloisCohomologyRepresentation N m t ℓ n σ) := by
  let e := geometricExponentIso N m mprime k t hm hbezout
  let g1 := geometricGaloisIso N 1 t σ
  let gm := geometricGaloisIso N m t σ
  have h : g1 ≪≫ e = e ≪≫ gm := by
    apply Iso.ext
    exact geometricExponentIso_galois N m mprime k t hm hbezout σ
  ext x
  calc
    AlgebraicGeometry.Scheme.ellAdicCohomologyEquiv g1 ℓ n
        (AlgebraicGeometry.Scheme.ellAdicCohomologyEquiv e ℓ n x) =
      AlgebraicGeometry.Scheme.ellAdicCohomologyEquiv (g1 ≪≫ e) ℓ n x :=
        (AlgebraicGeometry.Scheme.ellAdicCohomologyEquiv_trans ℓ g1 e n x).symm
    _ = AlgebraicGeometry.Scheme.ellAdicCohomologyEquiv (e ≪≫ gm) ℓ n x := by rw [h]
    _ = AlgebraicGeometry.Scheme.ellAdicCohomologyEquiv e ℓ n
        (AlgebraicGeometry.Scheme.ellAdicCohomologyEquiv gm ℓ n x) :=
          AlgebraicGeometry.Scheme.ellAdicCohomologyEquiv_trans ℓ e gm n x

variable {L : Type*} [Field L] [Algebra ℚ_[ℓ] L]

/-- The actual cohomological exponent-change pullback, rationalized and then
extended to the selected coefficient field `L`. -/
def geometricExponentCohomologyEquiv :
    GeometricCoefficientCohomology N m t ℓ (L := L) n ≃ₗ[L]
      GeometricCoefficientCohomology N 1 t ℓ (L := L) n :=
  (AlgebraicGeometry.Scheme.rationalEllAdicCohomologyEquiv
    (geometricExponentIso N m mprime k t hm hbezout) ℓ n).baseChange ℚ_[ℓ] L _ _

omit [NeZero N] in
/-- The coefficient-field transport is the scalar extension of the actual
integral cohomology pullback. -/
@[simp] theorem geometricExponentCohomologyEquiv_tmul
    (a : L) (b : ℚ_[ℓ])
    (x : (geometricAffineScheme N m t).EllAdicCohomology ℓ n) :
    geometricExponentCohomologyEquiv N m mprime k t hm hbezout ℓ (L := L) n
        (a ⊗ₜ[ℚ_[ℓ]] (b ⊗ₜ[ℤ_[ℓ]] x)) =
      a ⊗ₜ[ℚ_[ℓ]] (b ⊗ₜ[ℤ_[ℓ]]
        AlgebraicGeometry.Scheme.ellAdicCohomologyEquiv
          (geometricExponentIso N m mprime k t hm hbezout) ℓ n x) := rfl

/-- Intertwining of the two actual geometric deck representations after both
coefficient extensions. -/
theorem geometricExponentCohomologyEquiv_deck (ζ : rootsOfUnity N K) :
    (geometricCoefficientDeckRepresentation N 1 t ℓ (L := L) n ζ).comp
        (geometricExponentCohomologyEquiv N m mprime k t hm hbezout ℓ
          (L := L) n).toLinearMap =
      (geometricExponentCohomologyEquiv N m mprime k t hm hbezout ℓ
        (L := L) n).toLinearMap.comp
        (geometricCoefficientDeckRepresentation N m t ℓ (L := L) n (ζ ^ m)) := by
  have h := geometricExponentIntegralEquiv_deck N m mprime k t hm hbezout ℓ n ζ
  have hq := congrArg (fun f => LinearMap.baseChange ℚ_[ℓ] f) h
  have hL := congrArg (fun f => LinearMap.baseChange L f) hq
  change (LinearMap.baseChange L
      (LinearMap.baseChange ℚ_[ℓ]
        (geometricDeckCohomologyRepresentation N 1 t ℓ n ζ))).comp
      (LinearMap.baseChange L
        (LinearMap.baseChange ℚ_[ℓ]
          (geometricExponentIntegralEquiv N m mprime k t hm hbezout ℓ n).toLinearMap)) =
    (LinearMap.baseChange L
      (LinearMap.baseChange ℚ_[ℓ]
        (geometricExponentIntegralEquiv N m mprime k t hm hbezout ℓ n).toLinearMap)).comp
      (LinearMap.baseChange L
        (LinearMap.baseChange ℚ_[ℓ]
          (geometricDeckCohomologyRepresentation N m t ℓ n (ζ ^ m))))
  simpa only [LinearMap.baseChange_comp] using hL

omit [NeZero N] in
/-- The same coefficient-field transport is equivariant for the actual
algebraic Galois actions over the coefficient-field ground scheme. -/
theorem geometricExponentCohomologyEquiv_galois
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    (geometricCoefficientGaloisRepresentation N 1 t ℓ (L := L) n σ).comp
        (geometricExponentCohomologyEquiv N m mprime k t hm hbezout ℓ
          (L := L) n).toLinearMap =
      (geometricExponentCohomologyEquiv N m mprime k t hm hbezout ℓ
        (L := L) n).toLinearMap.comp
        (geometricCoefficientGaloisRepresentation N m t ℓ (L := L) n σ) := by
  have h := geometricExponentIntegralEquiv_galois N m mprime k t hm hbezout ℓ n σ
  have hq := congrArg (fun f => LinearMap.baseChange ℚ_[ℓ] f) h
  have hL := congrArg (fun f => LinearMap.baseChange L f) hq
  change (LinearMap.baseChange L
      (LinearMap.baseChange ℚ_[ℓ]
        (geometricGaloisCohomologyRepresentation N 1 t ℓ n σ))).comp
      (LinearMap.baseChange L
        (LinearMap.baseChange ℚ_[ℓ]
          (geometricExponentIntegralEquiv N m mprime k t hm hbezout ℓ n).toLinearMap)) =
    (LinearMap.baseChange L
      (LinearMap.baseChange ℚ_[ℓ]
        (geometricExponentIntegralEquiv N m mprime k t hm hbezout ℓ n).toLinearMap)).comp
      (LinearMap.baseChange L
        (LinearMap.baseChange ℚ_[ℓ]
          (geometricGaloisCohomologyRepresentation N m t ℓ n σ)))
  simpa only [LinearMap.baseChange_comp] using hL

variable [Fintype (rootsOfUnity N K)] [CharZero L]
  [FiniteDimensional ℚ_[ℓ] L]

/-- The base-cover label is the `m`th power of the chosen unpowered character.
The inverse power map from Bézout is used only to identify the finite sums. -/
def basePoweredDeckCharacter (ι : K →+* L) : rootsOfUnity N K →* Lˣ :=
  (coefficientDeckCharacter N ι).comp
    ((AdjoinRoot.rootsOfUnityPowEquiv N m mprime k hbezout).symm.toMonoidHom)

omit [NeZero N] [Fintype (rootsOfUnity N K)] [CharZero L] in
/-- The base-cover character evaluates as the `m`th power of the embedded
deck root, with the exponent occurring once. -/
theorem basePoweredDeckCharacter_apply (ι : K →+* L)
    (ζ : rootsOfUnity N K) :
    (basePoweredDeckCharacter N m mprime k hbezout ι ζ : L) =
      ι ((ζ : Kˣ) : K) ^ m := by
  change (coefficientDeckCharacter N ι (ζ ^ m) : L) =
    (coefficientDeckCharacter N ι ζ : L) ^ m
  simp only [map_pow, Units.val_pow_eq_pow_val]

/-- The explicit normalized character projector on the base geometric
Euler cover, labelled by `χ₀^m`. -/
def geometricBasePoweredProjector (ι : K →+* L) :
    GeometricCoefficientCohomology N 1 t ℓ (L := L) n →ₗ[L]
      GeometricCoefficientCohomology N 1 t ℓ (L := L) n :=
  Representation.characterProjector
    (basePoweredDeckCharacter N m mprime k hbezout ι)
    (geometricCoefficientDeckRepresentation N 1 t ℓ (L := L) n)

omit [CharZero L] [FiniteDimensional ℚ_[ℓ] L] in
/-- The base projector is the explicit average with the same `1/N`
normalization and the powered coefficient character. -/
theorem geometricBasePoweredProjector_formula {ζ : K}
    (hζ : IsPrimitiveRoot ζ N) (ι : K →+* L) :
    geometricBasePoweredProjector N m mprime k t hbezout ℓ n ι =
      ((N : L)⁻¹) • ∑ ξ : rootsOfUnity N K,
        ((basePoweredDeckCharacter N m mprime k hbezout ι ξ : L)⁻¹) •
          geometricCoefficientDeckRepresentation N 1 t ℓ (L := L) n ξ := by
  classical
  unfold geometricBasePoweredProjector Representation.characterProjector
  rw [card_deckGroup N hζ]

omit [FiniteDimensional ℚ_[ℓ] L] [CharZero L] in
/-- Every vector selected on the base cover has the `χ₀^m` deck eigenvalue. -/
theorem geometricBasePoweredProjector_eigen (ι : K →+* L)
    (ξ : rootsOfUnity N K)
    (v : GeometricCoefficientCohomology N 1 t ℓ (L := L) n) :
    geometricCoefficientDeckRepresentation N 1 t ℓ (L := L) n ξ
        (geometricBasePoweredProjector N m mprime k t hbezout ℓ n ι v) =
      ι ((ξ : Kˣ) : K) ^ m •
        geometricBasePoweredProjector N m mprime k t hbezout ℓ n ι v := by
  simpa only [geometricBasePoweredProjector, basePoweredDeckCharacter_apply] using
    (Representation.characterProjector_eigen
      (basePoweredDeckCharacter N m mprime k hbezout ι)
      (geometricCoefficientDeckRepresentation N 1 t ℓ (L := L) n) ξ v)

omit [CharZero L] [FiniteDimensional ℚ_[ℓ] L] in
/-- Exponent-change pullback conjugates the actual fixed primitive average
on the `m`-cover to the powered-character average on the base cover. The
equality reindexes all `N` deck parameters by the coprime power map. -/
theorem geometricExponentProjector_intertwine (ι : K →+* L) :
    (geometricBasePoweredProjector N m mprime k t hbezout ℓ n ι).comp
        (geometricExponentCohomologyEquiv N m mprime k t hm hbezout ℓ
          (L := L) n).toLinearMap =
      (geometricExponentCohomologyEquiv N m mprime k t hm hbezout ℓ
        (L := L) n).toLinearMap.comp
        (geometricFixedPrimitiveProjector N m t ℓ ι n) := by
  let e := (AdjoinRoot.rootsOfUnityPowEquiv (R := K) N m mprime k hbezout).symm
  apply Representation.characterProjector_comp_equiv
    (coefficientDeckCharacter N ι)
    (geometricCoefficientDeckRepresentation N m t ℓ (L := L) n)
    (geometricCoefficientDeckRepresentation N 1 t ℓ (L := L) n)
    e (geometricExponentCohomologyEquiv N m mprime k t hm hbezout ℓ (L := L) n)
  intro ζ
  simpa only [e, AdjoinRoot.rootsOfUnityPowEquiv_symm_apply] using
    (geometricExponentCohomologyEquiv_deck N m mprime k t hm hbezout ℓ
      (L := L) n ζ)

/-- The `χ₀` range on the actual geometric `m`-cover is linearly equivalent
to the `χ₀^m` range on the actual geometric base cover. -/
def geometricExponentProjectorRangeEquiv (ι : K →+* L) :
    (geometricFixedPrimitiveProjector N m t ℓ ι n).range ≃ₗ[L]
      (geometricBasePoweredProjector N m mprime k t hbezout ℓ n ι).range := by
  let e := (AdjoinRoot.rootsOfUnityPowEquiv (R := K) N m mprime k hbezout).symm
  exact Representation.characterProjectorRangeEquiv
    (coefficientDeckCharacter N ι)
    (geometricCoefficientDeckRepresentation N m t ℓ (L := L) n)
    (geometricCoefficientDeckRepresentation N 1 t ℓ (L := L) n)
    e (geometricExponentCohomologyEquiv N m mprime k t hm hbezout ℓ (L := L) n)
    (by
      intro ζ
      simpa only [e, AdjoinRoot.rootsOfUnityPowEquiv_symm_apply] using
        (geometricExponentCohomologyEquiv_deck N m mprime k t hm hbezout ℓ
          (L := L) n ζ))

omit [CharZero L] [FiniteDimensional ℚ_[ℓ] L] in
/-- Galois commutes with the powered projector on the geometric base cover
over the field containing the deck roots. -/
theorem geometricBasePoweredProjector_comm_galois (ι : K →+* L)
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    (geometricBasePoweredProjector N m mprime k t hbezout ℓ n ι).comp
        (geometricCoefficientGaloisRepresentation N 1 t ℓ (L := L) n σ) =
      (geometricCoefficientGaloisRepresentation N 1 t ℓ (L := L) n σ).comp
        (geometricBasePoweredProjector N m mprime k t hbezout ℓ n ι) := by
  exact Representation.characterProjector_comm
    (basePoweredDeckCharacter N m mprime k hbezout ι)
    (geometricCoefficientDeckRepresentation N 1 t ℓ (L := L) n)
    (geometricCoefficientGaloisRepresentation N 1 t ℓ (L := L) n σ)
    (fun ζ => geometricCoefficientDeckGalois_comm N 1 t ℓ (L := L) ζ σ n)

omit [CharZero L] [FiniteDimensional ℚ_[ℓ] L] in
/-- The powered base-character range is stable under ground-field Galois. -/
theorem geometricBasePoweredProjector_galois_mem_range (ι : K →+* L)
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    {v : GeometricCoefficientCohomology N 1 t ℓ (L := L) n}
    (hv : v ∈ (geometricBasePoweredProjector N m mprime k t hbezout ℓ n ι).range) :
    geometricCoefficientGaloisRepresentation N 1 t ℓ (L := L) n σ v ∈
      (geometricBasePoweredProjector N m mprime k t hbezout ℓ n ι).range := by
  rcases hv with ⟨w, rfl⟩
  refine ⟨geometricCoefficientGaloisRepresentation N 1 t ℓ (L := L) n σ w, ?_⟩
  exact congrArg (fun f : _ →ₗ[L] _ => f w)
    (geometricBasePoweredProjector_comm_galois N m mprime k t hbezout ℓ n ι σ)

omit [CharZero L] [FiniteDimensional ℚ_[ℓ] L] in
/-- The isomorphism of the two projector ranges respects algebraic Galois
over the field containing the deck roots. -/
theorem geometricExponentProjectorRangeEquiv_galois (ι : K →+* L)
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (v : (geometricFixedPrimitiveProjector N m t ℓ ι n).range) :
    geometricExponentProjectorRangeEquiv N m mprime k t hm hbezout ℓ n ι
        ⟨geometricCoefficientGaloisRepresentation N m t ℓ (L := L) n σ v.1,
          geometricFixedPrimitiveProjector_galois_mem_range N m t ℓ ι n σ v.2⟩ =
      ⟨geometricCoefficientGaloisRepresentation N 1 t ℓ (L := L) n σ
          (geometricExponentProjectorRangeEquiv N m mprime k t hm hbezout ℓ n ι v).1,
        geometricBasePoweredProjector_galois_mem_range N m mprime k t hbezout ℓ n
          ι σ (geometricExponentProjectorRangeEquiv N m mprime k t hm hbezout ℓ n ι v).2⟩ := by
  apply Subtype.ext
  change geometricExponentCohomologyEquiv N m mprime k t hm hbezout ℓ (L := L) n
      (geometricCoefficientGaloisRepresentation N m t ℓ (L := L) n σ v.1) =
    geometricCoefficientGaloisRepresentation N 1 t ℓ (L := L) n σ
      (geometricExponentCohomologyEquiv N m mprime k t hm hbezout ℓ (L := L) n v.1)
  exact (congrArg (fun f : _ →ₗ[L] _ => f v.1)
    (geometricExponentCohomologyEquiv_galois N m mprime k t hm hbezout ℓ
      (L := L) n σ)).symm

/-- On the cyclotomic ground field, the base projector uses the chosen
coefficient embedding with the `m`th-power label. -/
def cyclotomicGeometricBasePoweredProjector
    (t : Cyclotomic.cyclotomicField N)
    (ι : Cyclotomic.cyclotomicField N →+* L) :
    GeometricCoefficientCohomology N 1 t ℓ (L := L) n →ₗ[L]
      GeometricCoefficientCohomology N 1 t ℓ (L := L) n := by
  classical
  letI : Fintype (rootsOfUnity N (Cyclotomic.cyclotomicField N)) := Fintype.ofFinite _
  exact geometricBasePoweredProjector N m mprime k t hbezout ℓ n ι

omit [CharZero L] [FiniteDimensional ℚ_[ℓ] L] in
/-- The cyclotomic base projector is the normalized average indexed by the
actual deck roots, with the chosen primitive root proving its cardinality. -/
theorem cyclotomicGeometricBasePoweredProjector_formula
    (t : Cyclotomic.cyclotomicField N)
    (ι : Cyclotomic.cyclotomicField N →+* L) :
    cyclotomicGeometricBasePoweredProjector N m mprime k hbezout ℓ n t ι =
      letI : Fintype (rootsOfUnity N (Cyclotomic.cyclotomicField N)) := Fintype.ofFinite _
      ((N : L)⁻¹) • ∑ ξ : rootsOfUnity N (Cyclotomic.cyclotomicField N),
        ((basePoweredDeckCharacter N m mprime k hbezout ι ξ : L)⁻¹) •
          geometricCoefficientDeckRepresentation N 1 t ℓ (L := L) n ξ := by
  classical
  let : Fintype (rootsOfUnity N (Cyclotomic.cyclotomicField N)) := Fintype.ofFinite _
  exact geometricBasePoweredProjector_formula N m mprime k t hbezout ℓ n
    (Cyclotomic.root_isPrimitiveRoot N) ι

/-- The actual exponent-change pullback identifies the fixed cyclotomic
projector range with the powered base-character range. -/
def cyclotomicGeometricExponentProjectorRangeEquiv
    (t : Cyclotomic.cyclotomicField N)
    (ι : Cyclotomic.cyclotomicField N →+* L) :
    (cyclotomicGeometricFixedPrimitiveProjector N ℓ L m t ι n).range ≃ₗ[L]
      (cyclotomicGeometricBasePoweredProjector N m mprime k hbezout ℓ n t ι).range := by
  classical
  letI : Fintype (rootsOfUnity N (Cyclotomic.cyclotomicField N)) := Fintype.ofFinite _
  exact geometricExponentProjectorRangeEquiv N m mprime k t hm hbezout ℓ n ι

omit [CharZero L] [FiniteDimensional ℚ_[ℓ] L] in
/-- The powered base-character range is stable under the actual Galois
action over the cyclotomic field containing the deck roots. -/
theorem cyclotomicGeometricBasePoweredProjector_galois_mem_range
    (t : Cyclotomic.cyclotomicField N)
    (ι : Cyclotomic.cyclotomicField N →+* L)
    (σ : AlgebraicClosure (Cyclotomic.cyclotomicField N) ≃ₐ[
      Cyclotomic.cyclotomicField N]
      AlgebraicClosure (Cyclotomic.cyclotomicField N))
    {v : GeometricCoefficientCohomology N 1 t ℓ (L := L) n}
    (hv : v ∈ (cyclotomicGeometricBasePoweredProjector N m mprime k hbezout ℓ n t ι).range) :
    geometricCoefficientGaloisRepresentation N 1 t ℓ (L := L) n σ v ∈
      (cyclotomicGeometricBasePoweredProjector N m mprime k hbezout ℓ n t ι).range := by
  classical
  let : Fintype (rootsOfUnity N (Cyclotomic.cyclotomicField N)) := Fintype.ofFinite _
  exact geometricBasePoweredProjector_galois_mem_range N m mprime k t hbezout ℓ n ι σ hv

omit [CharZero L] [FiniteDimensional ℚ_[ℓ] L] in
/-- The actual cyclotomic exponent-change equivalence intertwines Galois on
the fixed `χ₀` range and the powered `χ₀^m` base range. -/
theorem cyclotomicGeometricExponentProjectorRangeEquiv_galois
    (t : Cyclotomic.cyclotomicField N)
    (ι : Cyclotomic.cyclotomicField N →+* L)
    (σ : AlgebraicClosure (Cyclotomic.cyclotomicField N) ≃ₐ[
      Cyclotomic.cyclotomicField N]
      AlgebraicClosure (Cyclotomic.cyclotomicField N))
    (v : (cyclotomicGeometricFixedPrimitiveProjector N ℓ L m t ι n).range) :
    cyclotomicGeometricExponentProjectorRangeEquiv N m mprime k hm hbezout ℓ n t ι
        ⟨geometricCoefficientGaloisRepresentation N m t ℓ (L := L) n σ v.1,
          cyclotomicGeometricFixedPrimitiveProjector_galois_mem_range N ℓ L m t ι n σ v.2⟩ =
      ⟨geometricCoefficientGaloisRepresentation N 1 t ℓ (L := L) n σ
          (cyclotomicGeometricExponentProjectorRangeEquiv N m mprime k hm hbezout ℓ n t ι v).1,
        cyclotomicGeometricBasePoweredProjector_galois_mem_range N m mprime k hbezout ℓ n
          t ι σ (cyclotomicGeometricExponentProjectorRangeEquiv N m mprime k hm hbezout ℓ n t ι v).2⟩ := by
  classical
  let : Fintype (rootsOfUnity N (Cyclotomic.cyclotomicField N)) := Fintype.ofFinite _
  exact geometricExponentProjectorRangeEquiv_galois N m mprime k t hm hbezout ℓ n ι σ v

end HilbertModularity.Hypergeometric.EulerCover
