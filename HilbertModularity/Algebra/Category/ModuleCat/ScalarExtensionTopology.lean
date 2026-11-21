/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.ScalarExtension.Continuity
public import HilbertModularity.Algebra.Category.ModuleCat.ScalarExtension

/-! # Continuous categorical scalar extension -/

@[expose] public noncomputable section
open scoped TensorProduct

namespace ModuleCat
open CategoryTheory
universe u v w z
variable {R : Type u} [CommRing R] [TopologicalSpace R]
  (S : Type v) [CommRing S] [TopologicalSpace S] [Algebra R S] [ContinuousSMul R S]
  {G : Type w} [Monoid G] [TopologicalSpace G]
  {V : Type z} [AddCommGroup V] [Module R V] [TopologicalSpace V] [IsModuleTopology R V]
  [TopologicalSpace ((extendScalars (algebraMap R S)).obj (ModuleCat.of R V))]
  [IsModuleTopology S ((extendScalars (algebraMap R S)).obj (ModuleCat.of R V))]

/-- Categorical scalar extension has continuous orbits for its canonical module topology. -/
theorem continuous_extendScalars_orbit (ρ : Representation R G V)
    (hρ : ∀ v : V, Continuous (fun g => ρ g v))
    (v : (extendScalars (algebraMap R S)).obj (ModuleCat.of R V)) :
    Continuous (fun g => ((extendScalars (algebraMap R S)).map (ModuleCat.ofHom (ρ g))).hom v) := by
  let : TopologicalSpace (S ⊗[R] V) := moduleTopology S (S ⊗[R] V)
  let : ContinuousAdd ((extendScalars (algebraMap R S)).obj (ModuleCat.of R V)) :=
    IsModuleTopology.toContinuousAdd S _
  let e := (extendScalarsTensorIso R S (ModuleCat.of R V)).toLinearEquiv
  have hc : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  apply (hc.comp (Representation.continuous_baseChange_orbit S ρ hρ (e v))).congr
  intro g
  have hn := extendScalarsTensorIso_naturality R S (ModuleCat.of R V) (ModuleCat.ofHom (ρ g))
  have hp := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hn) v
  change e (((extendScalars (algebraMap R S)).map (ModuleCat.ofHom (ρ g))).hom v) =
    ρ.baseChange S g (e v) at hp
  apply e.injective
  change e (e.symm (ρ.baseChange S g (e v))) = _
  exact (e.apply_symm_apply _).trans hp.symm

end ModuleCat
