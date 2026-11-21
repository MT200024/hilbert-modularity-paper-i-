/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.PrimePlusComplementIsogeny
public import HilbertModularity.Geometry.GroupScheme.PrimePlusComplementCharacter
public import HilbertModularity.Geometry.GroupScheme.PrimePlusComplementCorrespondence
public import HilbertModularity.Geometry.GroupScheme.PrimePlusRMComparison
public import HilbertModularity.RepresentationTheory.CharacterTwist

/-! # Tate comparison of the complementary plus fibres

The bridge below keeps Darmon--Mestre's geometric correspondence visible:
the map on the two actual rational Tate modules is conjugate to the Tate map
of the degree-`p` isogeny over the full cyclotomic field. The dihedral cover
data record the two quotient maps and the rotation used in Proposition 2.3.
Their conjugation sign is proved separately, before forming a twist.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry HilbertModularity.Cyclotomic
open scoped NumberField

namespace HilbertModularity.Hypergeometric

attribute [local instance] realPrimePowerCompletionPadicAlgebra

variable (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
  (ξ : ProjectiveLine.Parameter (realCyclotomicField p))

/-- Actual Tate realization of one fixed Darmon--Mestre correspondence.
The two coordinate equivalences are the standard finite-base-change Tate
identifications. `eta_on_full` requires the native map to be *the map induced
by the geometric isogeny*, rather than an arbitrarily chosen intertwiner.
The three covariance fields are the direct Galois action on the source's
`π₂`, `α`, and rotation correspondences. They do not state a twist. -/
structure PrimePlusDarmonMestreTateRealization
    (φDM : 𝓞 (realCyclotomicField p) →+* End (primePlusFamily p hp))
    (I : PrimePlusDarmonMestreGeometricData p hp ξ) where
  sourceRM_matches : ∀ a,
    I.sourceRM a = primePlusFullCyclotomicFiberEndomorphism p hp ξ (φDM a)
  cover : ModuleCat ℚ_[p]
  dihedral : DarmonMestreDihedralData p cover
    (primePlusDecompositionRepresentation p hp ξ)
    (primePlusDecompositionRepresentation p hp
      (ProjectiveLine.complementParameter (realCyclotomicField p) ξ))
  sourceCoordinate :
    primePlusDecompositionRepresentation p hp ξ ≃+
      GroupScheme.rationalTate (cyclotomicField p)
        (primePlusFullCyclotomicJacobian p hp ξ).X p
  targetCoordinate :
    primePlusDecompositionRepresentation p hp
      (ProjectiveLine.complementParameter (realCyclotomicField p) ξ) ≃+
        GroupScheme.rationalTate (cyclotomicField p)
          (primePlusFullCyclotomicJacobian p hp
            (ProjectiveLine.complementParameter (realCyclotomicField p) ξ)).X p
  sourceTrace_matches : ∀ w,
    sourceCoordinate (dihedral.sourceTrace w) =
      primePlusFullCyclotomicTateEndomorphism p hp ξ
        (I.sourceRM (tauInteger p 1)) (sourceCoordinate w)
  targetTrace_matches : ∀ u,
    targetCoordinate (dihedral.targetTrace u) =
      primePlusFullCyclotomicTateEndomorphism p hp
        (ProjectiveLine.complementParameter (realCyclotomicField p) ξ)
        (primePlusFullCyclotomicFiberEndomorphism p hp
          (ProjectiveLine.complementParameter (realCyclotomicField p) ξ)
          (φDM (tauInteger p 1))) (targetCoordinate u)
  etaTate : primePlusDecompositionRepresentation p hp ξ →ₗ[RealPrimePowerCompletion p 0]
    primePlusDecompositionRepresentation p hp
      (ProjectiveLine.complementParameter (realCyclotomicField p) ξ)
  eta_on_full : ∀ w, targetCoordinate (etaTate w) =
    GroupScheme.rationalTateMap (cyclotomicField p) p I.eta.hom.hom.hom
      (sourceCoordinate w)
  eta_dihedral : ∀ w, etaTate w = dihedral.eta w
  coverAction : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0) → cover →+ cover
  pi_galois : ∀ g w,
    dihedral.piPull
      ((primePlusDecompositionRepresentation p hp ξ).ρ g w) =
        coverAction g (dihedral.piPull w)
  alpha_galois : ∀ g v,
    dihedral.alphaPush (coverAction g v) =
      (primePlusDecompositionRepresentation p hp
        (ProjectiveLine.complementParameter (realCyclotomicField p) ξ)).ρ g
        (dihedral.alphaPush v)
  rotation_galois : ∀ g b v,
    dihedral.rotate b (coverAction g v) =
      coverAction g (dihedral.rotate
        ((primePlusLocalResidualCyclotomicCharacter p hp g : ZMod p) * b) v)

/-- [DarmonMestre, Proposition 2.1, correspondence (5), printed p. 307;
Proposition 2.3 and its proof, printed pp. 307--308], together with standard
rational Tate functoriality and finite base change, provides
the *same geometric map* and the quotient-map/rotation action on its Tate
realization. The completed RM-linearity uses the source trace correspondence
and one generic coefficient relabelling; it does not allow fibrewise labels.
The Tate isogeny step itself is formalized as
`GroupScheme.tateFiniteSurjectiveEquiv`; the admitted content is the
source-specific correspondence and its coherent realization on these fibres.
This is a named literature interface, not an ordinary or modularity premise.
-/
theorem primePlusDarmonMestreTateRealization_literature :
    ∃ φDM : 𝓞 (realCyclotomicField p) →+* End (primePlusFamily p hp),
      Function.Injective φDM ∧
      ∀ η : ProjectiveLine.Parameter (realCyclotomicField p),
        ∃ I : PrimePlusDarmonMestreGeometricData p hp η,
          Nonempty (PrimePlusDarmonMestreTateRealization p hp η φDM I) := by
  sorry

/-- A degree-`p` geometric isogeny induces an injective rational Tate map.
The proof uses the *actual* map in `eta_on_full` and the two field coordinates.
-/
theorem PrimePlusDarmonMestreTateRealization.etaTate_injective
    (φDM : 𝓞 (realCyclotomicField p) →+* End (primePlusFamily p hp))
    (I : PrimePlusDarmonMestreGeometricData p hp ξ)
    (T : PrimePlusDarmonMestreTateRealization p hp ξ φDM I) :
    Function.Injective T.etaTate := by
  let : IsFinite I.eta.hom.hom.hom.left := I.etaFinite
  let : Surjective I.eta.hom.hom.hom.left := I.etaSurjective
  intro v w h
  have hf := congrArg T.targetCoordinate h
  rw [T.eta_on_full, T.eta_on_full] at hf
  have hi := (GroupScheme.tateFiniteSurjectiveEquiv (cyclotomicField p)
    I.eta.hom.hom.hom p).injective
  exact T.sourceCoordinate.injective (hi hf)

/-- The source trace correspondence `ω=ζ+ζ⁻¹` is intertwined by the same
isogeny. Through `sourceTrace_matches` and `targetTrace_matches`, this is an
identity on the actual full-cyclotomic Tate maps of the selected plus
Jacobians; the index calculation `2a=1` is in `eta_intertwines_trace`. -/
theorem PrimePlusDarmonMestreTateRealization.etaTate_intertwines_trace
    (φDM : 𝓞 (realCyclotomicField p) →+* End (primePlusFamily p hp))
    (I : PrimePlusDarmonMestreGeometricData p hp ξ)
    (T : PrimePlusDarmonMestreTateRealization p hp ξ φDM I)
    (w : primePlusDecompositionRepresentation p hp ξ) :
    T.etaTate (T.dihedral.sourceTrace w) =
      T.dihedral.targetTrace (T.etaTate w) := by
  rw [T.eta_dihedral, T.eta_dihedral]
  exact T.dihedral.eta_intertwines_trace w

/-- On the same actual two fibres, conjugation of the source rotation
produces the quadratic sign. This is deduced from the source quotient-map
relations and the already identified local cyclotomic residual character.
-/
theorem PrimePlusDarmonMestreTateRealization.etaTate_galois_sign
    (φDM : 𝓞 (realCyclotomicField p) →+* End (primePlusFamily p hp))
    (I : PrimePlusDarmonMestreGeometricData p hp ξ)
    (T : PrimePlusDarmonMestreTateRealization p hp ξ φDM I)
    (g : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0))
    (w : primePlusDecompositionRepresentation p hp ξ) :
    T.etaTate ((primePlusDecompositionRepresentation p hp ξ).ρ g w) =
      (primePlusComplementQuadraticCharacter p hp g : RealPrimePowerCompletion p 0) •
        (primePlusDecompositionRepresentation p hp
          (ProjectiveLine.complementParameter (realCyclotomicField p) ξ)).ρ g
          (T.etaTate w) := by
  let ε := primePlusLocalResidualCyclotomicCharacter p hp
  have hs := T.dihedral.eta_galois_sign ε g T.coverAction
    (fun h => ((primePlusDecompositionRepresentation p hp ξ).ρ h).toAddMonoidHom)
    (fun h => ((primePlusDecompositionRepresentation p hp
      (ProjectiveLine.complementParameter (realCyclotomicField p) ξ)).ρ h).toAddMonoidHom)
    (T.pi_galois g) (T.alpha_galois g) (T.rotation_galois g) w
  rcases primePlusLocalResidualCyclotomicCharacter_eq_one_or_neg_one p hp g with h | h
  · have he := hs.1 h
    rw [← T.eta_dihedral, ← T.eta_dihedral] at he
    have hsource (u) :
        ((primePlusDecompositionRepresentation p hp ξ).ρ g).toAddMonoidHom u =
          (primePlusDecompositionRepresentation p hp ξ).ρ g u := rfl
    have htarget (u) :
        ((primePlusDecompositionRepresentation p hp
          (ProjectiveLine.complementParameter (realCyclotomicField p) ξ)).ρ g).toAddMonoidHom u =
            (primePlusDecompositionRepresentation p hp
              (ProjectiveLine.complementParameter (realCyclotomicField p) ξ)).ρ g u := rfl
    rw [hsource, htarget] at he
    rw [primePlusComplementQuadraticCharacter_of_residual_one p hp g h]
    simp only [Units.val_one, one_smul]
    exact he
  · have he := hs.2 h
    rw [← T.eta_dihedral, ← T.eta_dihedral] at he
    have hsource (u) :
        ((primePlusDecompositionRepresentation p hp ξ).ρ g).toAddMonoidHom u =
          (primePlusDecompositionRepresentation p hp ξ).ρ g u := rfl
    have htarget (u) :
        ((primePlusDecompositionRepresentation p hp
          (ProjectiveLine.complementParameter (realCyclotomicField p) ξ)).ρ g).toAddMonoidHom u =
            (primePlusDecompositionRepresentation p hp
              (ProjectiveLine.complementParameter (realCyclotomicField p) ξ)).ρ g u := rfl
    rw [hsource, htarget] at he
    rw [primePlusComplementQuadraticCharacter_of_residual_neg_one p hp g h]
    simp only [Units.val_neg, Units.val_one, neg_one_smul]
    exact he

/-- The geometric degree-`p` map becomes invertible on rational Tate, and
the proved dihedral conjugation sign gives the desired quadratic tensor
comparison of the *native completed RM factors*. This is the manuscript's
prime-level complementary-cusp deduction from the cited source data. -/
def primePlusComplementNativeTateEquiv
    (φDM : 𝓞 (realCyclotomicField p) →+* End (primePlusFamily p hp))
    (I : PrimePlusDarmonMestreGeometricData p hp ξ)
    (T : PrimePlusDarmonMestreTateRealization p hp ξ φDM I) :
    (((Representation.ofCharacter (primePlusComplementQuadraticCharacter p hp)).tprod
      (primePlusDecompositionRepresentation p hp
        (ProjectiveLine.complementParameter (realCyclotomicField p) ξ)).ρ).Equiv
      (primePlusDecompositionRepresentation p hp ξ).ρ) := by
  let W := primePlusDecompositionRepresentation p hp ξ
  let U := primePlusDecompositionRepresentation p hp
    (ProjectiveLine.complementParameter (realCyclotomicField p) ξ)
  let L := RealPrimePowerCompletion p 0
  letI : Module.Finite L W := Module.finite_of_finrank_eq_succ (by
    simpa only [Nat.reduceAdd] using finrank_primePlusDecompositionRepresentation p hp ξ)
  letI : Module.Finite L U := Module.finite_of_finrank_eq_succ (by
    simpa only [Nat.reduceAdd] using finrank_primePlusDecompositionRepresentation p hp
      (ProjectiveLine.complementParameter (realCyclotomicField p) ξ))
  have hfin : Module.finrank L W = Module.finrank L U := by
    rw [finrank_primePlusDecompositionRepresentation p hp ξ,
      finrank_primePlusDecompositionRepresentation p hp
        (ProjectiveLine.complementParameter (realCyclotomicField p) ξ)]
  have hinj := T.etaTate_injective p hp ξ φDM I
  have hsurj : Function.Surjective T.etaTate :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := T.etaTate) hfin).mp hinj
  let e : W ≃ₗ[L] U := LinearEquiv.ofBijective T.etaTate ⟨hinj, hsurj⟩
  apply Representation.characterTensorEquiv U.ρ W.ρ
    (primePlusComplementQuadraticCharacter p hp) e.symm
  intro g w
  have he0 := T.etaTate_galois_sign p hp ξ φDM I g (e.symm w)
  change e (W.ρ g (e.symm w)) =
    (primePlusComplementQuadraticCharacter p hp g : L) •
      U.ρ g (e (e.symm w)) at he0
  have he : e (W.ρ g (e.symm w)) =
      (primePlusComplementQuadraticCharacter p hp g : L) • U.ρ g w := by
    simpa only [e.apply_symm_apply] using he0
  have h := congrArg e.symm he
  simpa only [e.symm_apply_apply, map_smul] using h

/-- The generic full-endomorphism theorem compares the single source
correspondence action with the selected RM action by *one* automorphism of
the real integer ring. The equality is on the whole punctured family, so the
label does not change at individual fibres. -/
theorem primePlusDarmonMestreGlobalRMRelabelling
    (φDM : 𝓞 (realCyclotomicField p) →+* End (primePlusFamily p hp))
    (hφDM : Function.Injective φDM) :
    ∃ σ : 𝓞 (realCyclotomicField p) ≃+* 𝓞 (realCyclotomicField p),
      ∀ a, primePlusRealMultiplication p hp a = φDM (σ a) := by
  obtain ⟨σ, hfamily, _⟩ :=
    primePlusFamilyRMRelabelling_of_injective p hp φDM hφDM
  exact ⟨σ, hfamily⟩

/-- The manuscript's complementary-cusp comparison for the selected plus
family at prime conductor. The source supplies one correspondence action on
the whole family; the proof constructs one global RM relabelling and applies
the same quadratic local character at every punctured fibre. The conclusion
is a Tate comparison, not an ordinary or modularity assertion. -/
theorem exists_primePlusComplementNativeTateComparison :
    ∃ (φDM : 𝓞 (realCyclotomicField p) →+* End (primePlusFamily p hp))
      (σ : 𝓞 (realCyclotomicField p) ≃+* 𝓞 (realCyclotomicField p)),
      (∀ a, primePlusRealMultiplication p hp a = φDM (σ a)) ∧
      ∀ η : ProjectiveLine.Parameter (realCyclotomicField p),
        ∃ I : PrimePlusDarmonMestreGeometricData p hp η,
          (∀ a, I.sourceRM (σ a) =
            primePlusFullCyclotomicFiberEndomorphism p hp η
              (primePlusRealMultiplication p hp a)) ∧
          Nonempty ((((Representation.ofCharacter
            (primePlusComplementQuadraticCharacter p hp)).tprod
              (primePlusDecompositionRepresentation p hp
                (ProjectiveLine.complementParameter (realCyclotomicField p) η)).ρ).Equiv
              (primePlusDecompositionRepresentation p hp η).ρ)) := by
  obtain ⟨φDM, hφDM, hη⟩ := primePlusDarmonMestreTateRealization_literature p hp
  obtain ⟨σ, hσ⟩ := primePlusDarmonMestreGlobalRMRelabelling p hp φDM hφDM
  refine ⟨φDM, σ, hσ, ?_⟩
  intro η
  obtain ⟨I, ⟨T⟩⟩ := hη η
  refine ⟨I, ?_, ⟨primePlusComplementNativeTateEquiv p hp η φDM I T⟩⟩
  intro a
  rw [T.sourceRM_matches, ← hσ a]

/-- Ready-to-use local form for the deep-cusp ordinary application. Its
character is the explicit residual cyclotomic sign above, with continuity
and order-two proofs in `PrimePlusComplementCharacter`. -/
theorem nonempty_primePlusComplementNativeTateComparison :
    Nonempty ((((Representation.ofCharacter
      (primePlusComplementQuadraticCharacter p hp)).tprod
        (primePlusDecompositionRepresentation p hp
          (ProjectiveLine.complementParameter (realCyclotomicField p) ξ)).ρ).Equiv
        (primePlusDecompositionRepresentation p hp ξ).ρ)) := by
  obtain ⟨_, _, _, hη⟩ := exists_primePlusComplementNativeTateComparison p hp
  obtain ⟨_, _, e⟩ := hη ξ
  exact e

end HilbertModularity.Hypergeometric
