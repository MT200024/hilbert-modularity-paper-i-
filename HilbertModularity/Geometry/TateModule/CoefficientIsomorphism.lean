/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.TateModule.CoefficientDecomposition

/-! # Transport of a fixed Tate coefficient label

An isomorphism of group schemes intertwining their integral coefficient actions
identifies the same labelled Tate factors. This transports a good-reduction
model back to the original fibre in [TripathiGoswamiRevised,
Lemma `labelled-RM-compat`].
-/

public section
noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj NumberField TensorProduct

namespace AlgebraicGeometry.GroupScheme

universe u

variable (K : Type u) [Field K]
  {A B : Over (Spec (CommRingCat.of K))}
  [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
  (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [NumberField F]
  (L : Type*) [Field L] [Algebra ℚ_[p] L] [Algebra ℚ L]
  (hL : ∀ a : F, ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
  (φ : 𝓞 F →+* AddMonoid.End (Points K (AlgebraicClosure K) A))
  (ψ : 𝓞 F →+* AddMonoid.End (Points K (AlgebraicClosure K) B))
  (e : A ≅ B) [IsMonHom e.hom] [IsMonHom e.inv]
  (h : ∀ (a : 𝓞 F) (x : Points K (AlgebraicClosure K) A),
    pointsMap K (AlgebraicClosure K) e.hom (φ a x) =
      ψ a (pointsMap K (AlgebraicClosure K) e.hom x))

include h in
omit [NumberField F] in
/-- Compatibility with integral coefficients also holds for the inverse map. -/
theorem pointsAction_inverse_intertwines (a : 𝓞 F)
    (y : Points K (AlgebraicClosure K) B) :
    pointsMap K (AlgebraicClosure K) e.inv (ψ a y) =
      φ a (pointsMap K (AlgebraicClosure K) e.inv y) := by
  have hl (x : Points K (AlgebraicClosure K) A) :
      pointsMap K (AlgebraicClosure K) e.inv
        (pointsMap K (AlgebraicClosure K) e.hom x) = x := by
    have hx := DFunLike.congr_fun (pointsMap_comp K (AlgebraicClosure K) e.hom e.inv) x
    simpa only [Iso.hom_inv_id, pointsMap_id, AddMonoidHom.id_apply,
      AddMonoidHom.comp_apply] using hx.symm
  have hr (x : Points K (AlgebraicClosure K) B) :
      pointsMap K (AlgebraicClosure K) e.hom
        (pointsMap K (AlgebraicClosure K) e.inv x) = x := by
    have hx := DFunLike.congr_fun (pointsMap_comp K (AlgebraicClosure K) e.inv e.hom) x
    simpa only [Iso.inv_hom_id, pointsMap_id, AddMonoidHom.id_apply,
      AddMonoidHom.comp_apply] using hx.symm
  have hh := congrArg (pointsMap K (AlgebraicClosure K) e.inv)
    (h a (pointsMap K (AlgebraicClosure K) e.inv y))
  rw [hl, hr] at hh
  exact hh.symm

/-- The fixed-labelled Tate factor is invariant under a coefficient-compatible
isomorphism of the underlying group schemes. -/
def labelledTateEquiv
    (hφ : ∀ a, ∃ (f : A ⟶ A) (_ : IsMonHom f),
      φ a = pointsMap K (AlgebraicClosure K) f)
    (hψ : ∀ a, ∃ (f : B ⟶ B) (_ : IsMonHom f),
      ψ a = pointsMap K (AlgebraicClosure K) f)
    (σ : F →ₐ[ℚ] L) :
    (labelledTateSubrepresentation K A p F L hL φ hφ σ).toRepresentation.Equiv
      (labelledTateSubrepresentation K B p F L hL ψ hψ σ).toRepresentation := by
  let f := labelledTateIntertwiningMap K A p F L hL φ hφ ψ e.hom h hψ σ
  let g := labelledTateIntertwiningMap K B p F L hL ψ hψ φ e.inv
    (pointsAction_inverse_intertwines K F φ ψ e h) hφ σ
  have hl : Function.LeftInverse g f := by
    intro v
    apply Subtype.ext
    change (rationalTateMap K p e.inv).baseChange L
      ((rationalTateMap K p e.hom).baseChange L v.val) = v.val
    have hc := congrArg (fun z => LinearMap.baseChange L z)
      (rationalTateMap_comp K p e.hom e.inv)
    have hv := LinearMap.congr_fun hc v.val
    simpa only [Iso.hom_inv_id, rationalTateMap_id, LinearMap.baseChange_id,
      LinearMap.baseChange_comp, LinearMap.id_apply, LinearMap.comp_apply] using hv.symm
  have hr : Function.RightInverse g f := by
    intro v
    apply Subtype.ext
    change (rationalTateMap K p e.hom).baseChange L
      ((rationalTateMap K p e.inv).baseChange L v.val) = v.val
    have hc := congrArg (fun z => LinearMap.baseChange L z)
      (rationalTateMap_comp K p e.inv e.hom)
    have hv := LinearMap.congr_fun hc v.val
    simpa only [Iso.inv_hom_id, rationalTateMap_id, LinearMap.baseChange_id,
      LinearMap.baseChange_comp, LinearMap.id_apply, LinearMap.comp_apply] using hv.symm
  exact f.ofBijective ⟨hl.injective, hr.surjective⟩

end AlgebraicGeometry.GroupScheme
