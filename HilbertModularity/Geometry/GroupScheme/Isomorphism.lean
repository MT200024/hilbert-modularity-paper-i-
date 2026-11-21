/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.TateModule.Endomorphism
public import Mathlib.CategoryTheory.Monoidal.CommGrp_

/-! # Tate representations of isomorphic group schemes

An actual isomorphism of commutative group schemes induces an equivalence of
the integral and covariant rational Tate representations.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.GroupScheme

universe u
variable (K : Type u) [Field K] (p : ℕ) [Fact p.Prime]
  {A B : CommGrp (Over (Spec (CommRingCat.of K)))}

set_option backward.isDefEq.respectTransparency false in
/-- A group-scheme isomorphism induces an equivalence of its integral Tate representations. -/
def integralTateEquiv (e : A ≅ B) : (integralTateRepresentation K A.X p).Equiv (integralTateRepresentation K B.X p) := by
  let e' : A.X ≅ B.X := (CommGrp.forget _).mapIso e
  letI : IsMonHom e'.hom := inferInstanceAs (IsMonHom e.hom.hom.hom.hom)
  letI : IsMonHom e'.inv := inferInstanceAs (IsMonHom e.inv.hom.hom.hom)
  let f := integralTateIntertwiningMap K p e'.hom
  let g := integralTateIntertwiningMap K p e'.inv
  have hl : Function.LeftInverse g f := by
    intro v
    have h := LinearMap.congr_fun (integralTateMap_comp K p e'.hom e'.inv).symm v
    simpa only [Representation.IntertwiningMap.coe_mk, f, g, integralTateIntertwiningMap, Iso.hom_inv_id, integralTateMap_id, LinearMap.id_apply,
      LinearMap.comp_apply] using h
  have hr : Function.RightInverse g f := by
    intro v
    have h := LinearMap.congr_fun (integralTateMap_comp K p e'.inv e'.hom).symm v
    simpa only [Representation.IntertwiningMap.coe_mk, f, g, integralTateIntertwiningMap, Iso.inv_hom_id, integralTateMap_id, LinearMap.id_apply,
      LinearMap.comp_apply] using h
  exact f.ofBijective ⟨hl.injective, hr.surjective⟩

set_option backward.isDefEq.respectTransparency false in
/-- A group-scheme isomorphism induces an equivalence of its covariant rational Tate representations. -/
def tateEquiv (e : A ≅ B) : (tateRepresentation K A.X p).Equiv (tateRepresentation K B.X p) := by
  let e' : A.X ≅ B.X := (CommGrp.forget _).mapIso e
  letI : IsMonHom e'.hom := inferInstanceAs (IsMonHom e.hom.hom.hom.hom)
  letI : IsMonHom e'.inv := inferInstanceAs (IsMonHom e.inv.hom.hom.hom)
  let f := rationalTateIntertwiningMap K p e'.hom
  let g := rationalTateIntertwiningMap K p e'.inv
  have hl : Function.LeftInverse g f := by
    intro v
    have h := LinearMap.congr_fun (rationalTateMap_comp K p e'.hom e'.inv).symm v
    simpa only [Representation.IntertwiningMap.coe_mk, f, g, rationalTateIntertwiningMap, Iso.hom_inv_id, rationalTateMap_id, LinearMap.id_apply,
      LinearMap.comp_apply] using h
  have hr : Function.RightInverse g f := by
    intro v
    have h := LinearMap.congr_fun (rationalTateMap_comp K p e'.inv e'.hom).symm v
    simpa only [Representation.IntertwiningMap.coe_mk, f, g, rationalTateIntertwiningMap, Iso.inv_hom_id, rationalTateMap_id, LinearMap.id_apply,
      LinearMap.comp_apply] using h
  exact f.ofBijective ⟨hl.injective, hr.surjective⟩

end AlgebraicGeometry.GroupScheme
