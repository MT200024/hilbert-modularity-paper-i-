/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.CharacterComparison
public import HilbertModularity.RepresentationTheory.CharacterTwist
public import HilbertModularity.Geometry.Etale.ArithmeticProjectionKernel
public import HilbertModularity.Geometry.Etale.PathTransport
public import HilbertModularity.Geometry.Etale.LocalSystemPullback
public import HilbertModularity.Geometry.ProjectiveLine
public import HilbertModularity.CategoryTheory.Conjugation

/-! # Arithmetic comparison on the punctured parameter line

The arithmetic quotient here is induced by the structure map of the actual
punctured projective line. A rational parameter splits it. Consequently one
geometric comparison produces a single character of the base-field Galois
group, and its pullback is the same at every specialization section. This is
the representation-theoretic step in
[TripathiGoswamiRevised, Theorem RMgeneral].
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace Representation

variable {L G Γ V W : Type*} [Field L] [Group G] [Group Γ]
  [AddCommGroup V] [Module L V] [AddCommGroup W] [Module L W]

/-- An equivalence of representations stays an equivalence after tensoring
both sides with the same rank-one character. -/
def characterTensorEquivCongr {ρ : Representation L G V}
    {σ : Representation L G W} (χ : G →* Lˣ) (e : ρ.Equiv σ) :
    ((ofCharacter χ).tprod ρ).Equiv ((ofCharacter χ).tprod σ) := by
  let eTwist : (characterTwist ρ χ).Equiv (characterTwist σ χ) :=
    .mk e.toLinearEquiv (by
      intro g
      ext v
      change e ((χ g : L) • ρ g v) = (χ g : L) • σ g (e v)
      rw [map_smul]
      congr 1
      exact congrArg (fun f : V →ₗ[L] W => f v) (e.isIntertwining' g))
  exact (characterTwistTensorEquiv ρ χ).trans
    (eTwist.trans (characterTwistTensorEquiv σ χ).symm)

/-- Pullback of a generic character comparison needs only preservation of the
character, rather than a strict section of the arithmetic quotient. This is
the form used for geometric paths, whose projected Galois action is conjugate
to the original action. -/
def characterTensorEquivPullback (π : G →* Γ)
    (ρ : Representation L G V) (σ : Representation L G W)
    (ν : Γ →* Lˣ) (e : ((ofCharacter (ν.comp π)).tprod ρ).Equiv σ)
    (s : Γ →* G) (hν : ∀ g, ν (π (s g)) = ν g) :
    ((ofCharacter ν).tprod (ρ.comp s)).Equiv (σ.comp s) :=
  Equiv.mk e.toLinearEquiv fun g => by
    have he := e.isIntertwining' (s g)
    simpa only [tprod_apply, ofCharacter, MonoidHom.comp_apply, hν g] using he

/-- Transport both families along the same arithmetic path after pulling back
a generic comparison character. -/
def characterTensorEquivTransport
    {V' W' : Type*} [AddCommGroup V'] [Module L V']
    [AddCommGroup W'] [Module L W']
    (π : G →* Γ) (ρ : Representation L G V) (σ : Representation L G W)
    (ρ' : Representation L Γ V') (σ' : Representation L Γ W')
    (ν : Γ →* Lˣ) (e : ((ofCharacter (ν.comp π)).tprod ρ).Equiv σ)
    (s : Γ →* G) (hν : ∀ g, ν (π (s g)) = ν g)
    (eρ : Representation.Equiv (ρ.comp s) ρ')
    (eσ : Representation.Equiv (σ.comp s) σ') :
    ((ofCharacter ν).tprod ρ').Equiv σ' :=
  ((characterTensorEquivCongr ν eρ.symm).trans
    (characterTensorEquivPullback π ρ σ ν e s hν)).trans eσ

/-- A rank-one character is unchanged when a transported arithmetic section
projects to an inner conjugate of the original Galois action. -/
theorem character_comp_projection_of_conjugation (π : G →* Γ)
    (ν : Γ →* Lˣ) (s : Γ →* G) (a : Γ)
    (hs : ∀ g, π (s g) = a * g * a⁻¹) :
    ν.comp (π.comp s) = ν := by
  apply MonoidHom.ext
  intro g
  change ν (π (s g)) = ν g
  calc
    ν (π (s g)) = ν a * ν g * (ν a)⁻¹ := by rw [hs, map_mul, map_mul, map_inv]
    _ = ν g := by rw [mul_comm (ν a) (ν g), mul_assoc, mul_inv_cancel, mul_one]

end Representation

namespace Representation

/-- A geometric intertwiner descends to one continuous arithmetic character,
and the character is unchanged by transport to any section whose arithmetic
projection is conjugate to the identity. This is the Schur descent in
[GPRV, Lemma 8.22] used in
[TripathiGoswamiRevised, Theorem RMgeneral, steps 3--4]. -/
theorem exists_uniform_comparison_character
    {L G Γ V W : Type*} [NontriviallyNormedField L] [CharZero L] [CompleteSpace L]
    [Group G] [TopologicalSpace G] [ContinuousInv G] [CompactSpace G]
    [Group Γ] [TopologicalSpace Γ] [T2Space Γ]
    [NormedAddCommGroup V] [NormedSpace L V] [FiniteDimensional L V] [Nontrivial V]
    [NormedAddCommGroup W] [NormedSpace L W] [FiniteDimensional L W]
    (π : G →* Γ) (hπ : Function.Surjective π) (hπc : Continuous π)
    (ρRM : Representation L G V) (ρHGM : Representation L G W)
    (hRM : ∀ v, Continuous (fun g => ρRM g v))
    (hHGM : ∀ v, Continuous (fun g => ρHGM g v))
    (eGeom : Representation.Equiv (ρRM.comp π.ker.subtype)
      (ρHGM.comp π.ker.subtype))
    (Lbar : Type*) [Field Lbar] [Algebra L Lbar] [IsAlgClosed Lbar]
    [Representation.IsIrreducible (Representation.baseChange Lbar
      (ρRM.comp π.ker.subtype))] :
    ∃ ν : Γ →* Lˣ, Continuous ν ∧
      Nonempty (((Representation.ofCharacter (ν.comp π)).tprod ρRM).Equiv ρHGM) ∧
      ∀ (s : Γ →* G) (a : Γ),
        (∀ g, π (s g) = a * g * a⁻¹) →
        Nonempty (((Representation.ofCharacter ν).tprod (ρRM.comp s)).Equiv
          (ρHGM.comp s)) := by
  obtain ⟨ν, hν, ⟨e⟩⟩ :=
    exists_character_of_equiv_kernel_restriction π hπ hπc ρRM ρHGM eGeom hRM hHGM Lbar
  refine ⟨ν, hν, ⟨e⟩, ?_⟩
  intro s a hs
  exact ⟨characterTensorEquivPullback π ρRM ρHGM ν e s
    (fun g => by
      have h := congrArg (fun χ : Γ →* Lˣ => χ g)
        (character_comp_projection_of_conjugation π ν s a hs)
      simpa only [MonoidHom.comp_apply] using h)⟩

end Representation

namespace AlgebraicGeometry.Scheme

universe u
variable {S T : Scheme.{u}} (f : S ⟶ T) (K : Type u) [Field K]
  {x y : Spec (CommRingCat.of K) ⟶ S}

/-- The inverse étale fundamental-group equivalence sends the Galois loop
at the identity point back to its defining Galois automorphism. -/
theorem galoisEtaleFundamentalGroupEquiv_symm_galois [CharZero K]
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    (galoisEtaleFundamentalGroupEquiv K).symm
      (galoisToEtaleFundamentalGroup K (𝟙 _) g) = g := by
  apply (galoisEtaleFundamentalGroupEquiv K).injective
  rw [ContinuousMulEquiv.apply_symm_apply, galoisEtaleFundamentalGroupEquiv_apply]

/-- Mapping a path through a scheme morphism commutes with transport of
fundamental-group loops. -/
theorem etaleFundamentalGroupMap_arithmeticPath
    (e : finiteArithmeticFiberFunctor K x ≅ finiteArithmeticFiberFunctor K y)
    (σ : etaleFundamentalGroup K y) :
    etaleFundamentalGroupMap f K x
        ((etaleFundamentalGroupPathEquiv K S e).symm σ) =
      (etaleFundamentalGroupPathEquiv K T (etaleFiberPathMap f K e)).symm
        (etaleFundamentalGroupMap f K y σ) := by
  have hp : etaleFiberPath K S e ≫ etaleFiberPath K S σ =
      etaleFiberPath K S ((etaleFundamentalGroupPathEquiv K S e).symm σ) ≫
        etaleFiberPath K S e := by
    apply InducedCategory.hom_ext
    apply Core.hom_ext
    change e.hom ≫ σ.hom =
      ((etaleFundamentalGroupPathEquiv K S e).symm σ).hom ≫ e.hom
    change e.hom ≫ σ.hom = (e.symm.conjAut σ).hom ≫ e.hom
    rw [Iso.conjAut_hom, Iso.conj_apply]
    change e.hom ≫ σ.hom = e.hom ≫ σ.hom ≫ e.inv ≫ e.hom
    simp only [e.inv_hom_id, Category.comp_id]
  have hm := congrArg (etaleFiberGroupoidMap f K).map hp
  rw [Functor.map_comp, Functor.map_comp] at hm
  simp only [etaleFiberGroupoidMap_loop] at hm
  have ht : (etaleFiberPathMap f K e).hom ≫
      (etaleFundamentalGroupMap f K y σ).hom =
      (etaleFundamentalGroupMap f K x
        ((etaleFundamentalGroupPathEquiv K S e).symm σ)).hom ≫
        (etaleFiberPathMap f K e).hom := by
    exact congrArg (fun z => z.hom.iso.hom) hm
  exact (Iso.conjAut_symm_eq_of_intertwines (etaleFiberPathMap f K e) _ _ ht).symm

/-- For a path from one fibre to itself, loop transport is inner conjugation. -/
theorem etaleFundamentalGroupPathEquiv_self
    {x : Spec (CommRingCat.of K) ⟶ S}
    (e : finiteArithmeticFiberFunctor K x ≅ finiteArithmeticFiberFunctor K x)
    (σ : etaleFundamentalGroup K x) :
    (etaleFundamentalGroupPathEquiv K S e).symm σ =
      (show etaleFundamentalGroup K x from e)⁻¹ * σ *
        (show etaleFundamentalGroup K x from e) := by
  change e.symm.conjAut σ = _
  apply Iso.ext
  rw [Iso.conjAut_hom, Iso.conj_apply]
  rfl

private theorem cast_etaleFundamentalGroupMap_apply
    {p q : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K)}
    (h : p = q)
    (m : etaleFundamentalGroup K x →ₜ* etaleFundamentalGroup K p)
    (σ : etaleFundamentalGroup K x) :
    (show etaleFundamentalGroup K x →ₜ* etaleFundamentalGroup K q from by
      rw [h] at m
      exact m) σ = h ▸ m σ := by
  subst p
  rfl

/-- Projection to the arithmetic base sends path-transported Galois loops to
an inner conjugate of the original Galois element. The conjugator is the
image of the base path. -/
theorem etaleArithmeticProjection_alongPath
    {S : Scheme.{u}} (f : S ⟶ Spec (CommRingCat.of K))
    (x y : Spec (CommRingCat.of K) ⟶ S)
    (hx : x ≫ f = 𝟙 _) (hy : y ≫ f = 𝟙 _)
    (e : finiteArithmeticFiberFunctor K x ≅ finiteArithmeticFiberFunctor K y)
    [CharZero K] :
    ∃ a : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, ∀ g,
      etaleArithmeticProjection K f x hx (arithmeticLoopsAlongPath K S e g) =
        a * g * a⁻¹ := by
  have transport
      (p q : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K))
      (hp : p = 𝟙 _) (hq : q = 𝟙 _)
      (δ : finiteArithmeticFiberFunctor K p ≅ finiteArithmeticFiberFunctor K q)
      (σ : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) → etaleFundamentalGroup K p)
      (hσ : ∀ g, σ g = (etaleFundamentalGroupPathEquiv K _ δ).symm
        (galoisToEtaleFundamentalGroup K q g)) :
      ∃ a : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
        ∀ g, (galoisEtaleFundamentalGroupEquiv K).symm (hp ▸ σ g) =
          a * g * a⁻¹ := by
    subst p
    subst q
    refine ⟨((galoisEtaleFundamentalGroupEquiv K).symm δ)⁻¹, ?_⟩
    intro g
    rw [hσ, etaleFundamentalGroupPathEquiv_self]
    let d : etaleFundamentalGroup K (𝟙 (Spec (CommRingCat.of K))) := δ
    calc
      (galoisEtaleFundamentalGroupEquiv K).symm
          (d⁻¹ * galoisToEtaleFundamentalGroup K (𝟙 _) g * d) =
        ((galoisEtaleFundamentalGroupEquiv K).symm d)⁻¹ *
          (galoisEtaleFundamentalGroupEquiv K).symm
            (galoisToEtaleFundamentalGroup K (𝟙 _) g) *
          (galoisEtaleFundamentalGroupEquiv K).symm d := by
            rw [map_mul (galoisEtaleFundamentalGroupEquiv K).symm,
              map_mul (galoisEtaleFundamentalGroupEquiv K).symm,
              map_inv (galoisEtaleFundamentalGroupEquiv K).symm]
      _ = _ := by
        rw [galoisEtaleFundamentalGroupEquiv_symm_galois]
        simp only [d, inv_inv]
  have hproj (σ : etaleFundamentalGroup K x) :
      etaleArithmeticProjection K f x hx σ =
        (galoisEtaleFundamentalGroupEquiv K).symm
          (hx ▸ etaleFundamentalGroupMap f K x σ) := by
    unfold etaleArithmeticProjection
    exact congrArg (galoisEtaleFundamentalGroupEquiv K).symm
      (cast_etaleFundamentalGroupMap_apply K hx
        (etaleFundamentalGroupContinuousMap f K x) σ)
  let δ := etaleFiberPathMap f K e
  have hn (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :=
    etaleFundamentalGroupMap_arithmeticPath f K e
      (galoisToEtaleFundamentalGroup K y g)
  obtain ⟨a, ha⟩ := transport (x ≫ f) (y ≫ f) hx hy δ
    (fun g => etaleFundamentalGroupMap f K x (arithmeticLoopsAlongPath K S e g))
    (fun g => by
      change etaleFundamentalGroupMap f K x
        ((etaleFundamentalGroupPathEquiv K S e).symm
          (galoisToEtaleFundamentalGroup K y g)) = _
      rw [hn, etaleFundamentalGroupMap_galois])
  refine ⟨a, ?_⟩
  intro g
  rw [hproj]
  exact ha g

end AlgebraicGeometry.Scheme

namespace HilbertModularity.Hypergeometric

variable (K : Type*) [Field K] [CharZero K]

/-- The arithmetic quotient of the punctured line, based at an actual rational
parameter. -/
def puncturedArithmeticProjection (ξ₀ : ProjectiveLine.Parameter K) :
    Scheme.etaleFundamentalGroup K (ProjectiveLine.puncturedPoint K ξ₀) →ₜ*
      (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :=
  Scheme.etaleArithmeticProjection K (ProjectiveLine.puncturedToSpec K)
    (ProjectiveLine.puncturedPoint K ξ₀) (ProjectiveLine.puncturedPoint_toSpec K ξ₀)

/-- The group-homomorphism underlying the arithmetic projection. -/
@[expose] def puncturedArithmeticProjectionHom (ξ₀ : ProjectiveLine.Parameter K) :
    Scheme.etaleFundamentalGroup K (ProjectiveLine.puncturedPoint K ξ₀) →*
      (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :=
  (puncturedArithmeticProjection K ξ₀).toMonoidHom

/-- The punctured-line arithmetic quotient has the kernel of its structure map. -/
theorem puncturedArithmeticProjectionHom_ker (ξ₀ : ProjectiveLine.Parameter K) :
    (puncturedArithmeticProjectionHom K ξ₀).ker =
      (Scheme.etaleFundamentalGroupMap (ProjectiveLine.puncturedToSpec K) K
        (ProjectiveLine.puncturedPoint K ξ₀)).ker :=
  Scheme.etaleArithmeticProjection_ker K _ _ (ProjectiveLine.puncturedPoint_toSpec K ξ₀)

/-- The kernel of the arithmetic quotient of the punctured line. Identifying
this with the geometric fundamental group requires the étale exact sequence. -/
def puncturedArithmeticKernel (ξ₀ : ProjectiveLine.Parameter K) :
    Subgroup (Scheme.etaleFundamentalGroup K (ProjectiveLine.puncturedPoint K ξ₀)) :=
  (puncturedArithmeticProjectionHom K ξ₀).ker

/-- The Galois action at the chosen rational parameter splits the actual
arithmetic projection. -/
theorem puncturedArithmeticProjection_galois (ξ₀ : ProjectiveLine.Parameter K)
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    puncturedArithmeticProjection K ξ₀
      (Scheme.galoisToEtaleFundamentalGroup K (ProjectiveLine.puncturedPoint K ξ₀) g) = g :=
  Scheme.etaleArithmeticProjection_galois K (ProjectiveLine.puncturedToSpec K)
    (ProjectiveLine.puncturedPoint K ξ₀) (ProjectiveLine.puncturedPoint_toSpec K ξ₀) g

/-- The rational base point makes the arithmetic projection onto the actual
absolute Galois group surjective. -/
theorem puncturedArithmeticProjection_surjective (ξ₀ : ProjectiveLine.Parameter K) :
    Function.Surjective (puncturedArithmeticProjection K ξ₀) := by
  intro g
  exact ⟨Scheme.galoisToEtaleFundamentalGroup K
    (ProjectiveLine.puncturedPoint K ξ₀) g,
    puncturedArithmeticProjection_galois K ξ₀ g⟩

/-- The actual Galois loops at a rational point, transported to a fixed base
point of the punctured line. -/
@[expose] def puncturedArithmeticLoopsAlongPath (ξ₀ ξ : ProjectiveLine.Parameter K)
    (e : Scheme.finiteArithmeticFiberFunctor K (ProjectiveLine.puncturedPoint K ξ₀) ≅
      Scheme.finiteArithmeticFiberFunctor K (ProjectiveLine.puncturedPoint K ξ)) :
    (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →*
      Scheme.etaleFundamentalGroup K (ProjectiveLine.puncturedPoint K ξ₀) :=
  (Scheme.arithmeticLoopsAlongPath K (ProjectiveLine.punctured K) e).toMonoidHom

/-- At the base rational fibre, a character pulled back from the arithmetic
quotient is the original Galois character. -/
theorem puncturedArithmeticCharacter_galois (ξ₀ : ProjectiveLine.Parameter K)
    {L : Type*} [Field L]
    (ν : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →* Lˣ)
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    ν ((puncturedArithmeticProjection K ξ₀)
      (Scheme.galoisToEtaleFundamentalGroup K
        (ProjectiveLine.puncturedPoint K ξ₀) g)) = ν g := by
  rw [puncturedArithmeticProjection_galois]

/-- The arithmetic projection of a loop transported between rational fibres
is conjugate to the original Galois element. -/
theorem puncturedArithmeticProjection_alongPath
    (ξ₀ ξ : ProjectiveLine.Parameter K)
    (e : Scheme.finiteArithmeticFiberFunctor K (ProjectiveLine.puncturedPoint K ξ₀) ≅
      Scheme.finiteArithmeticFiberFunctor K (ProjectiveLine.puncturedPoint K ξ)) :
    ∃ a : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, ∀ g,
      puncturedArithmeticProjection K ξ₀
        (Scheme.arithmeticLoopsAlongPath K (ProjectiveLine.punctured K) e g) =
          a * g * a⁻¹ := by
  exact Scheme.etaleArithmeticProjection_alongPath K
    (ProjectiveLine.puncturedToSpec K)
    (ProjectiveLine.puncturedPoint K ξ₀) (ProjectiveLine.puncturedPoint K ξ)
    (ProjectiveLine.puncturedPoint_toSpec K ξ₀)
    (ProjectiveLine.puncturedPoint_toSpec K ξ) e

/-- The same quotient character is obtained along every arithmetic fibre
path. Its projected loop differs from the original Galois element by inner
conjugation, which leaves character values unchanged. -/
theorem puncturedArithmeticCharacter_alongPath
    (ξ₀ ξ : ProjectiveLine.Parameter K)
    (e : Scheme.finiteArithmeticFiberFunctor K (ProjectiveLine.puncturedPoint K ξ₀) ≅
      Scheme.finiteArithmeticFiberFunctor K (ProjectiveLine.puncturedPoint K ξ))
    {L : Type*} [Field L]
    (ν : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →* Lˣ)
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    ν (puncturedArithmeticProjection K ξ₀
      (Scheme.arithmeticLoopsAlongPath K (ProjectiveLine.punctured K) e g)) = ν g := by
  obtain ⟨a, hpath⟩ := puncturedArithmeticProjection_alongPath K ξ₀ ξ e
  rw [hpath, map_mul, map_mul, map_inv]
  rw [mul_comm (ν a) (ν g), mul_assoc, mul_inv_cancel, mul_one]

/-- On the actual punctured parameter line, a geometric comparison over the
kernel of the arithmetic projection produces one arithmetic character.
The geometric equivalence and absolute irreducibility remain explicit
hypotheses; identifying them with the chosen effective and dual RM families
is the geometric realization step of
[TripathiGoswamiRevised, Theorem RMgeneral]. -/
theorem exists_punctured_comparison_character
    (ξ₀ : ProjectiveLine.Parameter K)
    {L V W : Type*} [NontriviallyNormedField L] [CharZero L] [CompleteSpace L]
    [NormedAddCommGroup V] [NormedSpace L V] [FiniteDimensional L V] [Nontrivial V]
    [NormedAddCommGroup W] [NormedSpace L W] [FiniteDimensional L W]
    (ρRM : Representation L
      (Scheme.etaleFundamentalGroup K (ProjectiveLine.puncturedPoint K ξ₀)) V)
    (ρHGM : Representation L
      (Scheme.etaleFundamentalGroup K (ProjectiveLine.puncturedPoint K ξ₀)) W)
    (hRM : ∀ v, Continuous (fun g => ρRM g v))
    (hHGM : ∀ v, Continuous (fun g => ρHGM g v))
    (eGeom : Representation.Equiv
      (ρRM.comp (puncturedArithmeticProjectionHom K ξ₀).ker.subtype)
      (ρHGM.comp (puncturedArithmeticProjectionHom K ξ₀).ker.subtype))
    (Lbar : Type*) [Field Lbar] [Algebra L Lbar] [IsAlgClosed Lbar]
    [Representation.IsIrreducible (Representation.baseChange Lbar
      (ρRM.comp (puncturedArithmeticProjectionHom K ξ₀).ker.subtype))] :
    ∃ ν : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →* Lˣ,
      Continuous ν ∧
      Nonempty (((Representation.ofCharacter
        (ν.comp (puncturedArithmeticProjectionHom K ξ₀))).tprod ρRM).Equiv
          ρHGM) := by
  obtain ⟨ν, hν, he⟩ := Representation.exists_character_of_equiv_kernel_restriction
    (puncturedArithmeticProjectionHom K ξ₀)
      (puncturedArithmeticProjection_surjective K ξ₀)
      (puncturedArithmeticProjection K ξ₀).continuous ρRM ρHGM
      eGeom hRM hHGM Lbar
  exact ⟨ν, hν, he⟩

/-- Monodromy of a local system at a rational point of the punctured line. -/
@[expose] def puncturedFiberMonodromy
    (ξ : ProjectiveLine.Parameter K) {L : Type*} [Field L] [TopologicalSpace L]
    (F : Scheme.EtaleLocalSystem K (ProjectiveLine.punctured K) L) :=
  Scheme.fiberMonodromy K (ProjectiveLine.punctured K) F.algebraicFunctor
    (ProjectiveLine.puncturedPoint K ξ)

/-- The arithmetic action of a local system at a rational point. -/
@[expose] def puncturedFiberArithmeticRepresentation
    (ξ : ProjectiveLine.Parameter K) {L : Type*} [Field L] [TopologicalSpace L]
    (F : Scheme.EtaleLocalSystem K (ProjectiveLine.punctured K) L) :=
  F.arithmeticRepresentation (ProjectiveLine.puncturedPoint K ξ)

/-- The fibre path identifies the transported generic action of an étale local
system with its arithmetic action at the second rational point. -/
def puncturedArithmeticFiberPathEquiv
    (ξ₀ ξ : ProjectiveLine.Parameter K)
    (e : Scheme.finiteArithmeticFiberFunctor K (ProjectiveLine.puncturedPoint K ξ₀) ≅
      Scheme.finiteArithmeticFiberFunctor K (ProjectiveLine.puncturedPoint K ξ))
    {L : Type*} [Field L] [TopologicalSpace L]
    (F : Scheme.EtaleLocalSystem K (ProjectiveLine.punctured K) L) :
    Representation.Equiv
      ((puncturedFiberMonodromy K ξ₀ F).comp
        (puncturedArithmeticLoopsAlongPath K ξ₀ ξ e))
      (puncturedFiberArithmeticRepresentation K ξ F) :=
  Scheme.arithmeticFiberPathEquiv K (ProjectiveLine.punctured K) e F.algebraicFunctor

end HilbertModularity.Hypergeometric
