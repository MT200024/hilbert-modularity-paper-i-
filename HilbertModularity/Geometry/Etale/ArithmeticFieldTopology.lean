/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.ArithmeticFieldEquiv
public import HilbertModularity.Geometry.Etale.Field
public import Mathlib.FieldTheory.Galois.Profinite

/-! # Continuity of absolute Galois transport under field isomorphisms -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicClosure
universe u
variable (E K : Type u) [Field E] [Field K] [CharZero K] (σ : E ≃+* K)

/-- The closure-conjugation map is continuous for the native Krull topologies. -/
theorem continuous_galoisFieldEquiv : Continuous (galoisFieldEquiv E K σ) := by
  let x := AlgebraicGeometry.Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
    𝟙 (AlgebraicGeometry.Spec (CommRingCat.of E))
  let f := AlgebraicGeometry.Spec.map (CommRingCat.ofHom σ.symm.toRingHom)
  have hx : x ≫ f = 𝟙 (AlgebraicGeometry.Spec (CommRingCat.of K)) := by
    have h : CommRingCat.ofHom σ.symm.toRingHom ≫ CommRingCat.ofHom σ.toRingHom = 𝟙 _ := by
      ext a
      exact σ.apply_symm_apply a
    change (AlgebraicGeometry.Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ 𝟙 _) ≫
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom σ.symm.toRingHom) = _
    rw [Category.comp_id, ← AlgebraicGeometry.Spec.map_comp, h,
      AlgebraicGeometry.Spec.map_id]
  have hi := AlgebraicGeometry.Scheme.galoisToEtaleFundamentalGroup_isClosedEmbedding_of_section
    K f x hx
  rw [hi.isInducing.continuous_iff]
  have h := funext (AlgebraicGeometry.Scheme.arithmeticFiberFieldEquivIso_conj_galois
    E K σ (𝟙 (AlgebraicGeometry.Spec (CommRingCat.of E))))
  change Continuous (fun g => AlgebraicGeometry.Scheme.galoisToEtaleFundamentalGroup K x
    (galoisFieldEquiv E K σ g))
  rw [← h]
  exact (CategoryTheory.PreGaloisCategory.continuous_conjAut _).comp
    (AlgebraicGeometry.Scheme.continuous_galoisToEtaleFundamentalGroup E _)

/-- Field-coordinate transport is a topological group isomorphism in characteristic zero. -/
def continuousGaloisFieldEquiv [CharZero E] :
    (AlgebraicClosure E ≃ₐ[E] AlgebraicClosure E) ≃ₜ*
      (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) where
  __ := galoisFieldEquiv E K σ
  continuous_toFun := continuous_galoisFieldEquiv E K σ
  continuous_invFun := Continuous.continuous_symm_of_equiv_compact_to_t2
    (f := (galoisFieldEquiv E K σ).toEquiv) (continuous_galoisFieldEquiv E K σ)

end AlgebraicClosure
