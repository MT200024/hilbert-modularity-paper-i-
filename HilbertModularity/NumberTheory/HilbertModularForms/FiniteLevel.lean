/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.HilbertModularForms.CentralCharacter

/-! # Compact open finite level for adelic Hilbert forms

An adelic form is right invariant under a subgroup whose infinite component is
the identity and whose finite component is compact open. The subgroup is
retained in the full adelic group so the Hecke action and archimedean model use
the same function. See [SkinnerWiles, §4.5, Theorem A].
-/

public noncomputable section

open NumberField

namespace HilbertModularity.HilbertModularForms

variable (F : Type*) [Field F] [NumberField F]

/-- The finite adelic general linear group. -/
abbrev FiniteAdelicGL2 :=
  GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)

/-- Projection of an adelic invertible matrix to the finite adeles. -/
def finiteAdelicProjection : AdelicGL2 F →* FiniteAdelicGL2 F :=
  Matrix.GeneralLinearGroup.map
    (RingHom.snd (NumberField.InfiniteAdeleRing F)
      (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F))

/-- A genuine compact open finite adelic level, regarded in the full adelic
group with trivial infinite component. -/
structure FiniteLevel where
  subgroup : Subgroup (AdelicGL2 F)
  trivial_infinite : ∀ k ∈ subgroup, ∀ i j : Fin 2,
    ((k : Matrix (Fin 2) (Fin 2) (AdeleRing F)) i j).1 =
      (1 : Matrix (Fin 2) (Fin 2) (NumberField.InfiniteAdeleRing F)) i j
  finite_compact : IsCompact (finiteAdelicProjection F '' (subgroup : Set (AdelicGL2 F)))
  finite_open : IsOpen (finiteAdelicProjection F '' (subgroup : Set (AdelicGL2 F)))

end HilbertModularity.HilbertModularForms
