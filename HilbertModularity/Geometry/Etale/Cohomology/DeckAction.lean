/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.Cohomology.Galois

/-! # Base-changed automorphisms on actual cohomology

An automorphism over a ground scheme acts on the geometric fibre, and its
pullback commutes with the base-field Galois action. This is used for the
affine Euler deck projector of [TripathiGoswamiRevised].
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

open GroupScheme

universe u
variable {X Y B : Scheme.{u}} (p : X ⟶ B) (q : Y ⟶ B)

/-- An automorphism over the ground scheme acts on the second factor of an
actual scheme-theoretic base change. -/
def baseChangedIso (f : X ≅ X) (hf : f.hom ≫ p = p) :
    pullback q p ≅ pullback q p := by
  have hfi : f.inv ≫ p = p := by
    calc
      f.inv ≫ p = f.inv ≫ (f.hom ≫ p) := by rw [hf]
      _ = (f.inv ≫ f.hom) ≫ p := by rw [Category.assoc]
      _ = p := by simp
  refine
    { hom := pullback.lift (pullback.fst q p) (pullback.snd q p ≫ f.hom) ?_
      inv := pullback.lift (pullback.fst q p) (pullback.snd q p ≫ f.inv) ?_
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · simpa [Category.assoc, hf] using (pullback.condition (f := q) (g := p))
  · simpa [Category.assoc, hfi] using (pullback.condition (f := q) (g := p))
  · apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, Category.id_comp]
    · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
        f.hom_inv_id, Category.comp_id, Category.id_comp]
  · apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, Category.id_comp]
    · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
        f.inv_hom_id, Category.comp_id, Category.id_comp]

/-- The base-changed automorphism fixes the geometric-field projection. -/
@[simp] theorem baseChangedIso_fst (f : X ≅ X) (hf : f.hom ≫ p = p) :
    (baseChangedIso p q f hf).hom ≫ pullback.fst q p = pullback.fst q p := by
  simp only [baseChangedIso, pullback.lift_fst]

/-- The base-changed automorphism applies the original map on the Euler factor. -/
@[simp] theorem baseChangedIso_snd (f : X ≅ X) (hf : f.hom ≫ p = p) :
    (baseChangedIso p q f hf).hom ≫ pullback.snd q p =
      pullback.snd q p ≫ f.hom := by
  simp only [baseChangedIso, pullback.lift_snd]

variable (K E : Type u) [Field K] [Field E] [Algebra K E]
  {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of K))

/-- A ground-scheme automorphism commutes with algebraic Galois on the actual
geometric base change: the two maps act on different pullback factors. -/
theorem baseChangedIso_comm_fieldBaseChangeGaloisAut
    (f : X ≅ X) (hf : f.hom ≫ p = p) (σ : E ≃ₐ[K] E) :
    (baseChangedIso p (fieldPoint K E).hom f hf).hom ≫
        (fieldBaseChangeGaloisAut K E p σ).unop.hom =
      (fieldBaseChangeGaloisAut K E p σ).unop.hom ≫
        (baseChangedIso p (fieldPoint K E).hom f hf).hom := by
  apply pullback.hom_ext
  · simp only [Category.assoc, fieldBaseChangeGaloisAut_fst,
      baseChangedIso_fst]
    exact (Category.assoc _ _ _).symm.trans (congrArg
      (fun g => g ≫ Spec.map (CommRingCat.ofHom σ.toRingHom))
      (baseChangedIso_fst p (fieldPoint K E).hom f hf))
  · simp only [Category.assoc, fieldBaseChangeGaloisAut_snd,
      baseChangedIso_snd]
    simp only [← Category.assoc, fieldBaseChangeGaloisAut_snd]

/-- Pullback by a ground-scheme automorphism commutes with algebraic Galois
on the actual cohomology of the geometric base change. -/
theorem ellAdicCohomologyEquiv_baseChangedIso_comm_galois
    (f : X ≅ X) (hf : f.hom ≫ p = p) (σ : E ≃ₐ[K] E)
    (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ)
    (x : (pullback (fieldPoint K E).hom p).EllAdicCohomology ℓ n) :
    ellAdicCohomologyEquiv (baseChangedIso p (fieldPoint K E).hom f hf) ℓ n
        (ellAdicCohomologyEquiv
          (fieldBaseChangeGaloisAut K E p σ).unop ℓ n x) =
      ellAdicCohomologyEquiv
        (fieldBaseChangeGaloisAut K E p σ).unop ℓ n
        (ellAdicCohomologyEquiv (baseChangedIso p (fieldPoint K E).hom f hf) ℓ n x) := by
  let d := baseChangedIso p (fieldPoint K E).hom f hf
  let g := (fieldBaseChangeGaloisAut K E p σ).unop
  have h : d ≪≫ g = g ≪≫ d := by
    apply Iso.ext
    exact baseChangedIso_comm_fieldBaseChangeGaloisAut K E p f hf σ
  calc
    ellAdicCohomologyEquiv d ℓ n (ellAdicCohomologyEquiv g ℓ n x) =
        ellAdicCohomologyEquiv (d ≪≫ g) ℓ n x :=
          (ellAdicCohomologyEquiv_trans ℓ d g n x).symm
    _ = ellAdicCohomologyEquiv (g ≪≫ d) ℓ n x := by rw [h]
    _ = ellAdicCohomologyEquiv g ℓ n (ellAdicCohomologyEquiv d ℓ n x) :=
      ellAdicCohomologyEquiv_trans ℓ g d n x

end AlgebraicGeometry.Scheme
