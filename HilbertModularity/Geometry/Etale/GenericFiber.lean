/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.BaseChange
public import HilbertModularity.RingTheory.Etale.GenericFiber

/-! # Finite étale covers and the generic point of a normal affine scheme

Every map between the generic fibres of finite étale covers extends uniquely.
This is the scheme version of the integral-closure argument for their algebras.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme
universe u
variable (R F : Type u) [CommRing R] [IsIntegrallyClosed R]
  [Field F] [Algebra R F] [IsFractionRing R F]

/-- Every map of generic fibres extends to the original finite étale covers. -/
instance finiteEtalePullback_fractionField_full :
    (finiteEtalePullback (Spec.map (CommRingCat.ofHom (algebraMap R F)))).Full := by
  let P := finiteEtalePullback (Spec.map (CommRingCat.ofHom (algebraMap R F)))
  have : (finiteEtaleSpec R ⋙ P).Full :=
    Functor.Full.of_iso (finiteEtaleSpecBaseChangeIso R F).symm
  apply P.full_of_comp_essSurj (finiteEtaleSpec R)
  intro X Y f
  obtain ⟨g, hg⟩ := (finiteEtaleSpec R ⋙ P).map_surjective f
  exact ⟨(finiteEtaleSpec R).map g, hg⟩

/-- Two maps of finite étale covers agreeing at the generic point are equal. -/
instance finiteEtalePullback_fractionField_faithful :
    (finiteEtalePullback (Spec.map (CommRingCat.ofHom (algebraMap R F)))).Faithful := by
  let P := finiteEtalePullback (Spec.map (CommRingCat.ofHom (algebraMap R F)))
  have : (finiteEtaleSpec R ⋙ P).Faithful :=
    Functor.Faithful.of_iso (finiteEtaleSpecBaseChangeIso R F).symm
  apply P.faithful_of_comp_essSurj (finiteEtaleSpec R)
  intro X Y f g h
  have he : (finiteEtaleSpec R).preimage f = (finiteEtaleSpec R).preimage g := by
    apply (finiteEtaleSpec R ⋙ P).map_injective
    simpa only [Functor.comp_map, Functor.map_preimage] using h
  simpa only [Functor.map_preimage] using congrArg (finiteEtaleSpec R).map he

end AlgebraicGeometry.Scheme
