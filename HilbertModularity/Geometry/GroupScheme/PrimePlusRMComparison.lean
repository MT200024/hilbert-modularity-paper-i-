/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.PrimePlusDarmonMestreJacobian
public import HilbertModularity.NumberTheory.IntegralAction
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced

/-! # The selected plus action and Darmon--Mestre's generic action

Darmon--Mestre's full generic endomorphism-ring calculation is about a specified
correspondence action on the Chebyshev Jacobian [DarmonMestre, Proposition 2.1,
printed p. 306]. The selected plus Jacobian is that pointed curve after
`s = 2t - 1`, but its chosen integral action is independent. The statements
below derive faithful generic restriction and fullness of the selected action,
then compare it with any supplied full correspondence action by one coefficient
relabelling. The curve identity alone does not identify the coefficient labels.
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped NumberField

namespace AlgebraicGeometry

/-- Smooth scheme morphisms have geometrically reduced fibres. This standard
literature input combines [src_stacks_smooth_reduced, Tag 01VB] (smoothness
is stable under base change) with [src_stacks_smooth_reduced, Tag 056T]
(a scheme smooth over a field is geometrically reduced), applied to each
residue-field fibre. The total-space reduction below uses Mathlib's flat/fibre
criterion separately. -/
theorem smooth_geometricallyReduced_literature {X Y : Scheme}
    (f : X ⟶ Y) [Smooth f] : GeometricallyReduced f := by
  sorry

end AlgebraicGeometry

namespace HilbertModularity.Hypergeometric

open HilbertModularity.Cyclotomic HilbertModularity.Hyperelliptic
  AlgebraicGeometry.GroupScheme

/-- Restriction of endomorphisms of the selected plus family to its generic fibre. -/
@[expose] def primePlusGenericEndMap (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :=
  fiberEndomorphismMap (RatFunc (realCyclotomicField p)) (primePlusFamily p hp)
    (ProjectiveLine.puncturedRationalPoint (realCyclotomicField p))

/-- The generic fibre detects endomorphisms of the selected smooth abelian
scheme. Smoothness gives flatness and geometrically reduced fibres; the
punctured projective line is reduced and locally Noetherian, so the total
space is reduced. The generic-point pullback is dominant, and separatedness
then extends equality of its endomorphisms to the family. -/
theorem primePlusGenericEndMap_injective (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    Function.Injective (primePlusGenericEndMap p hp) := by
  intro f g hfg
  apply CommGrp.hom_ext
  apply Over.OverMorphism.ext
  let : Smooth (primePlusFamily p hp).X.hom :=
    SmoothOfRelativeDimension.smooth (Module.finrank ℚ (realCyclotomicField p)) _
  let : Flat (primePlusFamily p hp).X.hom := inferInstance
  let : GeometricallyReduced (primePlusFamily p hp).X.hom :=
    smooth_geometricallyReduced_literature _
  let : IsReduced (primePlusFamily p hp).X.left :=
    GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian
      (primePlusFamily p hp).X.hom
  let : IsSchemeTheoreticallyDominant
      (ProjectiveLine.puncturedRationalPoint (realCyclotomicField p)) := by
    let : IsDominant
        (ProjectiveLine.puncturedRationalPoint (realCyclotomicField p)) := inferInstance
    exact IsSchemeTheoreticallyDominant.of_isDominant _
  let : IsSchemeTheoreticallyDominant
      (pullback.fst (primePlusFamily p hp).X.hom
        (ProjectiveLine.puncturedRationalPoint (realCyclotomicField p))) :=
    IsSchemeTheoreticallyDominant.pullbackFst _ _
  let : IsSeparated ((primePlusFamily p hp).X.hom) := inferInstance
  let : IsDominant
      (pullback.fst (primePlusFamily p hp).X.hom
        (ProjectiveLine.puncturedRationalPoint (realCyclotomicField p))) := inferInstance
  exact ext_of_isDominant_of_isSeparated
    (f := f.hom.hom.hom.left)
    (g := g.hom.hom.hom.left)
    (primePlusFamily p hp).X.hom (by
      exact (f.hom.hom.hom.w).trans (g.hom.hom.hom.w).symm)
    (pullback.fst (primePlusFamily p hp).X.hom
      (ProjectiveLine.puncturedRationalPoint (realCyclotomicField p))) (by
        have hh := congrArg
          (fun u : End (fiber (RatFunc (realCyclotomicField p))
            (primePlusFamily p hp)
            (ProjectiveLine.puncturedRationalPoint (realCyclotomicField p))) =>
              u.hom.hom.hom.left) hfg
        simp only [primePlusGenericEndMap, fiberEndomorphismMap] at hh
        change ((Over.pullback
          (ProjectiveLine.puncturedRationalPoint (realCyclotomicField p))).map
            f.hom.hom.hom).left =
          ((Over.pullback
          (ProjectiveLine.puncturedRationalPoint (realCyclotomicField p))).map
            g.hom.hom.hom).left at hh
        have hu := congrArg
          (fun u => u ≫ pullback.fst (primePlusFamily p hp).X.hom
            (ProjectiveLine.puncturedRationalPoint (realCyclotomicField p))) hh
        simpa only [Over.pullback_map_left, pullback.lift_fst] using hu)

/-- The **generic** full endomorphism ring of the Chebyshev Jacobian `J₂`
is isomorphic to `𝓞 K_p`. The geometric computation is [TTV, Theorem 1 and
the remark after Section 2]; descent of all generic endomorphisms to `K_p`
is [DarmonMestre, Proposition 2.1, printed pp. 306--307]. Darmon--Mestre
also specify an action by correspondence (5), with `ω` acting as `ηζ`, but
this interface records only the full-ring isomorphism, not that specified
action. Here `s = 2t - 1`; no full-ring assertion is made for specialized
fibres. This named literature interface is a conditional premise. -/
theorem darmonMestreChebyshevGenericEndomorphisms
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (J : CommGrp (Over (Spec (CommRingCat.of
      (RatFunc (realCyclotomicField p))))))
    (b : Over.mk (𝟙 (Spec (CommRingCat.of
        (RatFunc (realCyclotomicField p))))) ⟶
      Over.mk (darmonMestreChebyshevCurveToSpec p
        (primePlusData p hp).p_odd
        (plusGenericParameter (realCyclotomicField p))))
    (hJ : GroupScheme.PointedCurveJacobian (RatFunc (realCyclotomicField p))
      (Over.mk (darmonMestreChebyshevCurveToSpec p
        (primePlusData p hp).p_odd
        (plusGenericParameter (realCyclotomicField p)))) b J) :
    ∃ φDM : 𝓞 (realCyclotomicField p) →+* End J,
      Function.Bijective φDM := by
  sorry

/-- Apply the generic Chebyshev endomorphism theorem to the same selected
plus Jacobian, using its already established pointed-curve identity. -/
theorem primePlusDarmonMestreGenericEndomorphisms
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    ∃ φDM : 𝓞 (realCyclotomicField p) →+*
      End (fiber (RatFunc (realCyclotomicField p)) (primePlusFamily p hp)
        (ProjectiveLine.puncturedRationalPoint (realCyclotomicField p))),
      Function.Bijective φDM := by
  let q := primePlusDarmonMestreGenericJacobian p hp
  exact darmonMestreChebyshevGenericEndomorphisms p hp _ q.1 q.2

/-- The full generic-ring calculation gives a ring equivalence for the
*selected* Jacobian, after the exact Chebyshev parameter substitution.  This
uses only the cited generic calculation; it says nothing about the selected
integral action or an individual specialized fibre. -/
theorem primePlusDarmonMestreGenericEndEquiv
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    Nonempty (𝓞 (realCyclotomicField p) ≃+*
      End (fiber (RatFunc (realCyclotomicField p)) (primePlusFamily p hp)
        (ProjectiveLine.puncturedRationalPoint (realCyclotomicField p)))) := by
  obtain ⟨φDM, hφDM⟩ := primePlusDarmonMestreGenericEndomorphisms p hp
  exact ⟨RingEquiv.ofBijective φDM hφDM⟩

/-- Once the full generic endomorphism ring is identified with the cyclotomic
integers and generic restriction is faithful, the selected integral action
differs from that identification by one coefficient automorphism. This is the
algebraic deduction needed after [DarmonMestre, Proposition 2.1, p. 306]. -/
theorem primePlusGenericRMRelabelling (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (e : 𝓞 (realCyclotomicField p) ≃+*
      End (fiber (RatFunc (realCyclotomicField p)) (primePlusFamily p hp)
        (ProjectiveLine.puncturedRationalPoint (realCyclotomicField p))))
    (hres : Function.Injective (primePlusGenericEndMap p hp)) :
    ∃ σ : 𝓞 (realCyclotomicField p) ≃+* 𝓞 (realCyclotomicField p),
      ∀ a, primePlusGenericEndMap p hp (primePlusRealMultiplication p hp a) =
        e (σ a) := by
  let f := (primePlusGenericEndMap p hp).comp (primePlusRealMultiplication p hp)
  have hf : Function.Injective f :=
    hres.comp (primePlusData p hp).realMultiplication_injective
  exact NumberField.RingOfIntegers.exists_equiv_of_injective e f hf

/-- The selected integral action already exhausts the full generic
endomorphism ring. Its injectivity comes from the chosen family and faithful
generic restriction; surjectivity follows from the generic full-ring theorem
and the fact that an injective self-map of `𝓞 K_p` is an automorphism. This
does not identify the labels with correspondence (5). -/
theorem primePlusGenericRMAction_bijective (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    Function.Bijective
      ((primePlusGenericEndMap p hp).comp (primePlusRealMultiplication p hp)) := by
  let hres := primePlusGenericEndMap_injective p hp
  obtain ⟨e⟩ := primePlusDarmonMestreGenericEndEquiv p hp
  obtain ⟨σ, hσ⟩ := primePlusGenericRMRelabelling p hp e hres
  constructor
  · exact hres.comp (primePlusData p hp).realMultiplication_injective
  · intro u
    obtain ⟨a, rfl⟩ := e.surjective u
    obtain ⟨b, rfl⟩ := σ.surjective a
    exact ⟨b, hσ b⟩

/-- Every endomorphism of the selected family is its chosen integral RM
action. The conclusion concerns this family over the punctured parameter
line; it does not claim the same full-ring property for individual fibres. -/
theorem primePlusFamilyRMAction_bijective (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    Function.Bijective (primePlusRealMultiplication p hp) := by
  let hres := primePlusGenericEndMap_injective p hp
  let hgen := primePlusGenericRMAction_bijective p hp
  constructor
  · exact (primePlusData p hp).realMultiplication_injective
  · intro u
    obtain ⟨a, ha⟩ := hgen.2 (primePlusGenericEndMap p hp u)
    exact ⟨a, hres ha⟩

/-- The chosen action gives the full endomorphism ring of the selected
punctured family, conditional on the cited generic full-ring computation. -/
def primePlusFamilyRMEquiv (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    𝓞 (realCyclotomicField p) ≃+* End (primePlusFamily p hp) :=
  RingEquiv.ofBijective (primePlusRealMultiplication p hp)
    (primePlusFamilyRMAction_bijective p hp)

/-- Generic restriction is an equivalence for this selected punctured family.
Surjectivity uses the full generic Chebyshev endomorphism calculation
[DarmonMestre, Proposition 2.1, printed p. 306], together with the selected
faithful integral action. This concerns the generic fibre, not the full
endomorphism ring of any specialized fibre. -/
theorem primePlusGenericEndMap_bijective
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    Function.Bijective (primePlusGenericEndMap p hp) := by
  constructor
  · exact primePlusGenericEndMap_injective p hp
  · intro u
    obtain ⟨a, ha⟩ := (primePlusGenericRMAction_bijective p hp).2 u
    exact ⟨primePlusRealMultiplication p hp a, ha⟩

/-- Every generic endomorphism of the selected Jacobian extends uniquely to
its smooth family over the punctured line. The extension is obtained from the
already chosen integral action and the full generic ring calculation. -/
def primePlusGenericEndEquiv
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    End (primePlusFamily p hp) ≃+*
      End (fiber (RatFunc (realCyclotomicField p)) (primePlusFamily p hp)
        (ProjectiveLine.puncturedRationalPoint (realCyclotomicField p))) :=
  RingEquiv.ofBijective (primePlusGenericEndMap p hp)
    (primePlusGenericEndMap_bijective p hp)

/-- A specified generic RM action on this Jacobian has a unique extension to
the selected family. Thus a source that identifies the *particular*
Darmon--Mestre correspondence with a generic ring equivalence can be applied
on every fibre without separately assuming its extension. The present theorem
does not identify that correspondence with an unspecified generic equivalence. -/
theorem primePlusSpecifiedGenericAction_lift
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (e : 𝓞 (realCyclotomicField p) ≃+*
      End (fiber (RatFunc (realCyclotomicField p)) (primePlusFamily p hp)
        (ProjectiveLine.puncturedRationalPoint (realCyclotomicField p)))) :
    ∃! φ : 𝓞 (realCyclotomicField p) →+* End (primePlusFamily p hp),
      ∀ a, primePlusGenericEndMap p hp (φ a) = e a := by
  let φ : 𝓞 (realCyclotomicField p) →+* End (primePlusFamily p hp) :=
    (e.trans (primePlusGenericEndEquiv p hp).symm).toRingHom
  refine ⟨φ, ?_, ?_⟩
  · intro a
    exact (primePlusGenericEndEquiv p hp).apply_symm_apply (e a)
  · intro ψ hψ
    apply RingHom.ext
    intro a
    apply primePlusGenericEndMap_injective p hp
    exact (hψ a).trans ((primePlusGenericEndEquiv p hp).apply_symm_apply (e a)).symm

/-- If Darmon--Mestre's correspondence acts on this same family and gives the
specified full generic endomorphism ring, the selected family action equals it
after one relabelling. Generic faithfulness then carries that equality to every
fibre; it does not assert that an arbitrary specialized fibre has a full
endomorphism ring. -/
theorem primePlusFamilyRMRelabelling (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (e : 𝓞 (realCyclotomicField p) ≃+*
      End (fiber (RatFunc (realCyclotomicField p)) (primePlusFamily p hp)
        (ProjectiveLine.puncturedRationalPoint (realCyclotomicField p))))
    (φDM : 𝓞 (realCyclotomicField p) →+* End (primePlusFamily p hp))
    (hDM : ∀ a, primePlusGenericEndMap p hp (φDM a) = e a)
    (hres : Function.Injective (primePlusGenericEndMap p hp)) :
    ∃ σ : 𝓞 (realCyclotomicField p) ≃+* 𝓞 (realCyclotomicField p),
      (∀ a, primePlusRealMultiplication p hp a = φDM (σ a)) ∧
      (∀ (L : Type) [Field L]
        (x : Spec (CommRingCat.of L) ⟶
          ProjectiveLine.punctured (realCyclotomicField p)) (a),
        fiberEndomorphismMap L (primePlusFamily p hp) x
          (primePlusRealMultiplication p hp a) =
        fiberEndomorphismMap L (primePlusFamily p hp) x (φDM (σ a))) := by
  obtain ⟨σ, hσ⟩ := primePlusGenericRMRelabelling p hp e hres
  have hfamily (a : 𝓞 (realCyclotomicField p)) :
      primePlusRealMultiplication p hp a = φDM (σ a) := by
    apply hres
    exact (hσ a).trans (hDM (σ a)).symm
  exact ⟨σ, hfamily, fun L _ x a => congrArg
    (fiberEndomorphismMap L (primePlusFamily p hp) x) (hfamily a)⟩

/-- Any faithful integral RM action on this same punctured family agrees with
its selected action after one coefficient relabelling, uniformly at all fibres.
The generic endomorphism calculation supplies the full family ring internally;
no fullness assumption on the second action or on specialized fibres is needed. -/
theorem primePlusFamilyRMRelabelling_of_injective
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (φDM : 𝓞 (realCyclotomicField p) →+* End (primePlusFamily p hp))
    (hDM : Function.Injective φDM) :
    ∃ σ : 𝓞 (realCyclotomicField p) ≃+* 𝓞 (realCyclotomicField p),
      (∀ a, primePlusRealMultiplication p hp a = φDM (σ a)) ∧
      (∀ (L : Type) [Field L]
        (x : Spec (CommRingCat.of L) ⟶
          ProjectiveLine.punctured (realCyclotomicField p)) (a),
        fiberEndomorphismMap L (primePlusFamily p hp) x
          (primePlusRealMultiplication p hp a) =
        fiberEndomorphismMap L (primePlusFamily p hp) x (φDM (σ a))) := by
  obtain ⟨τ, hτ⟩ := NumberField.RingOfIntegers.exists_equiv_of_injective
    (primePlusFamilyRMEquiv p hp) φDM hDM
  have hfamily (a : 𝓞 (realCyclotomicField p)) :
      primePlusRealMultiplication p hp a = φDM (τ.symm a) := by
    simpa only [RingEquiv.apply_symm_apply, primePlusFamilyRMEquiv,
      RingEquiv.ofBijective_apply] using (hτ (τ.symm a)).symm
  exact ⟨τ.symm, hfamily, fun L _ x a => congrArg
    (fiberEndomorphismMap L (primePlusFamily p hp) x) (hfamily a)⟩

/-- A specified extension of Darmon--Mestre's generic correspondence to the
chosen punctured family identifies its action with the selected one after one
integral coefficient relabelling.  The remaining hypothesis is that this
specified family action gives the full generic endomorphism ring. Faithfulness
of generic restriction is derived internally. The cited abstract generic-ring
isomorphism does not identify the particular correspondence action. -/
theorem primePlusFamilyRMRelabelling_ofDarmonMestre
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (φDM : 𝓞 (realCyclotomicField p) →+* End (primePlusFamily p hp))
    (hDM : Function.Bijective
      ((primePlusGenericEndMap p hp).comp φDM)) :
    ∃ σ : 𝓞 (realCyclotomicField p) ≃+* 𝓞 (realCyclotomicField p),
      (∀ a, primePlusRealMultiplication p hp a = φDM (σ a)) ∧
      (∀ (L : Type) [Field L]
        (x : Spec (CommRingCat.of L) ⟶
          ProjectiveLine.punctured (realCyclotomicField p)) (a),
        fiberEndomorphismMap L (primePlusFamily p hp) x
          (primePlusRealMultiplication p hp a) =
        fiberEndomorphismMap L (primePlusFamily p hp) x (φDM (σ a))) := by
  let e := RingEquiv.ofBijective ((primePlusGenericEndMap p hp).comp φDM) hDM
  exact primePlusFamilyRMRelabelling p hp e φDM (fun _ => rfl)
    (primePlusGenericEndMap_injective p hp)

/-- A *specified* generic ring identification lifts uniquely to the selected
family and is one coefficient automorphism away from its chosen RM action.
The equality then specializes to every field-valued fibre of this same
family. Applied to [DarmonMestre, Proposition 2.1, printed p. 306], the
specified identification still has to be verified to be their correspondence
(5); the mere existence of an isomorphism does not fix that label. -/
theorem primePlusSpecifiedGenericAction_specializes
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (e : 𝓞 (realCyclotomicField p) ≃+*
      End (fiber (RatFunc (realCyclotomicField p)) (primePlusFamily p hp)
        (ProjectiveLine.puncturedRationalPoint (realCyclotomicField p)))) :
    ∃ (φ : 𝓞 (realCyclotomicField p) →+* End (primePlusFamily p hp))
      (σ : 𝓞 (realCyclotomicField p) ≃+* 𝓞 (realCyclotomicField p)),
      Function.Bijective φ ∧
      (∀ a, primePlusGenericEndMap p hp (φ a) = e a) ∧
      (∀ a, primePlusRealMultiplication p hp a = φ (σ a)) ∧
      (∀ (L : Type) [Field L]
        (x : Spec (CommRingCat.of L) ⟶
          ProjectiveLine.punctured (realCyclotomicField p)) (a),
        fiberEndomorphismMap L (primePlusFamily p hp) x
          (primePlusRealMultiplication p hp a) =
        fiberEndomorphismMap L (primePlusFamily p hp) x (φ (σ a))) := by
  let Φ := e.trans (primePlusGenericEndEquiv p hp).symm
  let φ := Φ.toRingHom
  have hφ (a : 𝓞 (realCyclotomicField p)) :
      primePlusGenericEndMap p hp (φ a) = e a :=
    (primePlusGenericEndEquiv p hp).apply_symm_apply (e a)
  obtain ⟨σ, hfamily, hfibers⟩ :=
    primePlusFamilyRMRelabelling p hp e φ hφ
      (primePlusGenericEndMap_injective p hp)
  exact ⟨φ, σ, Φ.bijective, hφ, hfamily, hfibers⟩

end HilbertModularity.Hypergeometric
