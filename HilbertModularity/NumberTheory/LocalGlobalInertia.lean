/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.PadicCompletion
public import HilbertModularity.NumberTheory.PadicInertia
public import HilbertModularity.RepresentationTheory.FiniteCharacterRamification
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Local restriction at a number-field prime

The local field is the actual completion at the specified prime. The chosen
embedding of the global algebraic closure defines restriction. For abelian
characters the image of inertia is independent of the prime over the base
prime, by conjugacy and the local/global comparison.
-/

public noncomputable section

open IsDedekindDomain
open scoped NumberField

namespace NumberField

variable (F : Type) [Field F] [NumberField F]

/-- The rational prime below a finite prime of a number field. -/
def primeBelow (q : HeightOneSpectrum (𝓞 F)) : ℕ :=
  Rat.HeightOneSpectrum.natGenerator (q.under ℤ)

instance primeBelow_prime (q : HeightOneSpectrum (𝓞 F)) : Fact (primeBelow F q).Prime :=
  ⟨Rat.HeightOneSpectrum.prime_natGenerator _⟩

/-- The prime below is obtained by contraction to the rational integers. -/
instance liesOver_primeBelow (q : HeightOneSpectrum (𝓞 F)) :
    q.asIdeal.LiesOver (Ideal.span {(primeBelow F q : ℤ)}) := by
  have hs := Rat.HeightOneSpectrum.span_natGenerator (q.under ℤ)
  have he : Rat.IsIntegralClosure.intEquiv ℤ = RingEquiv.refl ℤ := by
    ext x
    exact map_intCast (Rat.IsIntegralClosure.intEquiv ℤ) x
  rw [he] at hs
  change Ideal.span {(primeBelow F q : ℤ)} =
    Ideal.map (RingHom.id ℤ) (q.asIdeal.under ℤ) at hs
  rw [Ideal.map_id] at hs
  rw [hs]
  infer_instance

end NumberField

namespace NumberField.LocalGalois

variable (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F]
  (q : HeightOneSpectrum (𝓞 F)) [q.asIdeal.LiesOver (Ideal.span {(p : ℤ)})]

/-- An algebraic embedding of the actual finite coefficient completion into `Qp`-bar. -/
def completionEmbedding :
    q.adicCompletion F →ₐ[ℚ_[p]] PadicAlgCl p := IsAlgClosed.lift

/-- The algebraic embedding is continuous for the actual completion topology. -/
theorem continuous_completionEmbedding :
    Continuous (completionEmbedding p F q) :=
  (completionEmbedding p F q).toLinearMap.continuous_of_finiteDimensional

/-- The completion is a closed embedded local field inside the algebraic p-adic numbers. -/
theorem isClosedEmbedding_completionEmbedding :
    Topology.IsClosedEmbedding (completionEmbedding p F q) :=
  LinearMap.isClosedEmbedding_of_injective
    (f := (completionEmbedding p F q).toLinearMap)
    (LinearMap.ker_eq_bot.mpr (completionEmbedding p F q).injective)

/-- The chosen completion embedding, as an algebra structure. -/
@[instance_reducible] def completionPadicAlgebra :
    Algebra (q.adicCompletion F) (PadicAlgCl p) :=
  (completionEmbedding p F q).toAlgebra

attribute [local instance] completionPadicAlgebra

/-- The completion embedding respects the original rational p-adic scalars. -/
theorem completionPadicTower :
    IsScalarTower ℚ_[p] (q.adicCompletion F) (PadicAlgCl p) :=
  IsScalarTower.of_algebraMap_eq fun a => (completionEmbedding p F q).commutes a |>.symm

attribute [local instance] completionPadicTower

/-- The global number field embedded through its specified completion. -/
@[instance_reducible] def globalPadicAlgebra :
    Algebra F (PadicAlgCl p) :=
  ((completionEmbedding p F q).toRingHom.comp
    (algebraMap F (q.adicCompletion F))).toAlgebra



/-- This global embedding factors through the actual completion map. -/
theorem globalPadicTower :
    letI := globalPadicAlgebra p F q
    IsScalarTower F
      (q.adicCompletion F) (PadicAlgCl p) := by
  let := globalPadicAlgebra p F q
  exact IsScalarTower.of_algebraMap_eq fun _ => rfl



/-- Extend the fixed global embedding to the global algebraic closure. -/
def algebraicClosureEmbedding :
    letI := globalPadicAlgebra p F q
    AlgebraicClosure F →ₐ[F]
      PadicAlgCl p := by
  letI := globalPadicAlgebra p F q
  letI : Module.IsTorsionFree F (PadicAlgCl p) :=
    DivisionSemiring.to_moduleIsTorsionFree
  exact IsAlgClosed.lift

/-- The extended embedding as an algebra structure for normal restriction. -/
@[instance_reducible] def algebraicClosurePadicAlgebra :
    Algebra (AlgebraicClosure F) (PadicAlgCl p) :=
  (algebraicClosureEmbedding p F q).toAlgebra



/-- The extended embedding agrees with the chosen embedding on the global field. -/
theorem algebraicClosurePadicTower :
    letI := globalPadicAlgebra p F q
    letI := algebraicClosurePadicAlgebra p F q
    IsScalarTower F
      (AlgebraicClosure F) (PadicAlgCl p) := by
  let := globalPadicAlgebra p F q
  let := algebraicClosurePadicAlgebra p F q
  exact IsScalarTower.of_algebraMap_eq fun a => (algebraicClosureEmbedding p F q).commutes a |>.symm



/-- Restriction from the actual local Galois group to the global absolute Galois group. -/
def localGaloisRestriction :
    Gal(PadicAlgCl p/q.adicCompletion F) →*
      Gal(AlgebraicClosure F/F) := by
  letI := globalPadicAlgebra p F q
  letI := globalPadicTower p F q
  letI := algebraicClosurePadicAlgebra p F q
  letI := algebraicClosurePadicTower p F q
  exact (AlgEquiv.restrictNormalHom _).comp (AlgEquiv.restrictScalarsHom _)

/-- Restriction is characterized by its action on the embedded global algebraic closure. -/
theorem localGaloisRestriction_commutes
    (g : Gal(PadicAlgCl p/q.adicCompletion F))
    (x : AlgebraicClosure F) :
    algebraicClosureEmbedding p F q (localGaloisRestriction p F q g x) =
      g (algebraicClosureEmbedding p F q x) := by
  let := globalPadicAlgebra p F q
  let := globalPadicTower p F q
  let := algebraicClosurePadicAlgebra p F q
  let := algebraicClosurePadicTower p F q
  exact (g.restrictScalars F).restrictNormal_commutes _ x

open IntermediateField in
/-- Local restriction is continuous for the actual Krull topologies. -/
theorem continuous_localGaloisRestriction :
    Continuous (localGaloisRestriction p F q) := by
  classical
  let := globalPadicAlgebra p F q
  let := globalPadicTower p F q
  let C := q.adicCompletion F
  let f := algebraicClosureEmbedding p F q
  let : Algebra.IsAlgebraic C (PadicAlgCl p) :=
    Algebra.IsAlgebraic.tower_top (K := ℚ_[p]) C
  apply continuous_of_continuousAt_one (localGaloisRestriction p F q)
  rw [ContinuousAt, map_one]
  refine ((galGroupBasis C (PadicAlgCl p)).nhds_one_hasBasis.tendsto_iff
    (galGroupBasis F (AlgebraicClosure F)).nhds_one_hasBasis).mpr ?_
  rintro _ ⟨_, ⟨L, hL : FiniteDimensional _ _, rfl⟩, rfl⟩
  refine ⟨_, ⟨_, ⟨adjoin C (L.map f), ?_, rfl⟩, rfl⟩, fun g hg x => ?_⟩
  · suffices Algebra.EssFiniteType C (adjoin C (L.map f : Set (PadicAlgCl p))) by
      apply Algebra.finite_of_essFiniteType_of_isAlgebraic
    replace hL : Algebra.EssFiniteType F L := inferInstance
    rw [essFiniteType_iff] at hL ⊢
    obtain ⟨s, rfl⟩ := hL
    use s.image f
    rw [adjoin_map, adjoin_adjoin_right, Finset.coe_image]
  · apply f.injective
    exact (localGaloisRestriction_commutes p F q g x).trans
      (hg ⟨f x, subset_adjoin _ _ ⟨_, x.2, rfl⟩⟩)

/-- Completion identifies local inertia with global inertia up to conjugacy.
After applying an abelian character, conjugacy disappears, so the image is the
same for every prime over `q`.

This is the infinite-Galois corollary of [MilneANT, Proposition 8.10 and the
following inertia diagram, pp.139–140; Proposition 8.13, p.141], together with
conjugacy of primes over a fixed prime. Passage through finite Galois extensions
uses [MilneFT, Theorem 7.13]. The embedding used by `localGaloisRestriction`
is the one constructed above through the actual completion. This standard
comparison makes no assertion about finiteness, Hodge weights or modularity. -/
theorem character_inertia_range_eq
    {A : Type*} [CommGroup A]
    (χ : HilbertModularity.HilbertModularForms.AbsoluteGalois F →* A)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver q.asIdeal] :
    Set.range (χ.comp (Q.inertia
      (HilbertModularity.HilbertModularForms.AbsoluteGalois F)).subtype) =
    Set.range ((χ.comp (localGaloisRestriction p F q)).comp
      (PadicAlgCl.inertia p (q.adicCompletion F)).subtype) := by
  sorry

/-- One finite local inertia image supplies a positive exponent valid at
all global primes over the given prime. -/
theorem exists_uniform_inertia_exponent
    {A : Type*} [CommGroup A]
    (χ : HilbertModularity.HilbertModularForms.AbsoluteGalois F →* A)
    (hfin : (Set.range ((χ.comp (localGaloisRestriction p F q)).comp
      (PadicAlgCl.inertia p (q.adicCompletion F)).subtype)).Finite) :
    ∃ n : ℕ, 0 < n ∧ ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))),
      Q.IsMaximal → Q.LiesOver q.asIdeal →
      ∀ g : HilbertModularity.HilbertModularForms.AbsoluteGalois F,
        g ∈ Q.inertia (HilbertModularity.HilbertModularForms.AbsoluteGalois F) →
        χ g ^ n = 1 := by
  let η := (χ.comp (localGaloisRestriction p F q)).comp
    (PadicAlgCl.inertia p (q.adicCompletion F)).subtype
  let : Finite η.range := hfin.to_subtype
  refine ⟨Nat.card η.range, Nat.card_pos, ?_⟩
  intro Q hQ hOver g hg
  let := hQ
  let := hOver
  have hm : χ g ∈ η.range := by
    change χ g ∈ Set.range η
    rw [← character_inertia_range_eq p F q χ Q]
    exact ⟨⟨g, hg⟩, rfl⟩
  exact congrArg Subtype.val (pow_card_eq_one' (x := (⟨χ g, hm⟩ : η.range)))

end NumberField.LocalGalois
