/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.PrimePlusSelectedResidualData
public import HilbertModularity.Hypergeometric.PrimePlusDeepCuspChecklist
public import HilbertModularity.Hypergeometric.PrimePlusTateContinuity
public import HilbertModularity.Geometry.GroupScheme.PrimePlusTateDeterminantComparison
public import HilbertModularity.NumberTheory.RealCyclotomicQuadratic
public import HilbertModularity.RepresentationTheory.Irreducibility

/-! # The selected plus Jacobian's Skinner–Wiles lattice

The field action and residual action below come from one integral Tate basis of
the selected plus Jacobian. The finite ramification row follows from the
abelian-variety literature input. Other arithmetic and local comparison inputs
remain visible at the application boundary.
-/

public section
noncomputable section

open scoped NumberField Pointwise ValuativeRel TensorProduct
open ValuativeRel NumberField AlgebraicGeometry AlgebraicGeometry.GroupScheme
  CategoryTheory
open IsDedekindDomain

namespace HilbertModularity.Hypergeometric

open HilbertModularity.Cyclotomic HilbertModularity.HilbertModularForms
  IsNonarchimedeanLocalField

attribute [local instance] HilbertModularity.Cyclotomic.realFieldAlgebra

/-- Coordinates supplied by the selected Jacobian's integral Tate basis
identify its field action with the base-changed native action. -/
def primePlusTateFieldCoordinateEquiv
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    {E : Type*} [Field E] [ValuativeRel E]
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E]
    (β : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[E])
    (hβ : (inferInstance : Algebra (AdicCompletion
      (Ideal.span {realPrimeGenerator p}) (𝓞 (realCyclotomicField p))) E) =
      ((𝒪[E]).subtype.comp β).toAlgebra) :
    letI := primePlusIntegralTateModule p hp ξ
    (primePlusTateFieldCoordinateAction p hp ξ β).Equiv
      ((primePlusIntegralTateRepresentation p hp ξ).baseChange E) := by
  letI := primePlusIntegralTateModule p hp ξ
  cases hβ
  letI : Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E :=
    ((𝒪[E]).subtype.comp β).toAlgebra
  let b := (primePlusIntegralTateBasis p hp ξ).baseChange E
  refine Representation.Equiv.mk b.equivFun.symm ?_
  intro g
  apply LinearMap.ext
  intro v
  have h := LinearMap.congr_fun
    (primePlusTateFieldCoordinateAction_apply p hp ξ β g) v
  change b.equivFun.symm ((primePlusTateFieldCoordinateAction p hp ξ β) g v) =
    ((primePlusIntegralTateRepresentation p hp ξ).baseChange E g)
      (b.equivFun.symm v)
  apply b.equivFun.injective
  simpa only [b,
    LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply,
    LinearEquiv.conjRingEquiv_apply_apply] using h

/-- The selected Jacobian's residual datum and its canonical-prime kernel
have the same matrix because both come from the chosen integral Tate basis. -/
theorem primePlusSelectedTateResidualMatrix
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    {E : Type*} [Field E] [ValuativeRel E]
    (β : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[E])
    (κ : (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) ≃+*
      (𝒪[E] ⧸ 𝓂[E]))
    (D : SkinnerWilesResidualData (primePlusTateFieldCoordinateAction p hp ξ β))
    (g : AbsoluteGalois (realCyclotomicField p)) :
    letI := primePlusIntegralTateModule p hp ξ
    letI := (AdicCompletion.evalOneₐ
      (Ideal.span {realPrimeGenerator p}) : _).toRingHom.toAlgebra
    (LinearMap.toMatrix (primePlusResidualTateBasis p hp ξ)
      (primePlusResidualTateBasis p hp ξ)
      ((primePlusIntegralTateRepresentation p hp ξ).baseChange
        (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) g)).map
          κ.toRingHom =
      (LinearMap.toMatrix' (D.integralAction g)).map
        (Ideal.Quotient.mk (𝓂[E])) := by
  let := primePlusIntegralTateModule p hp ξ
  let := (AdicCompletion.evalOneₐ
    (Ideal.span {realPrimeGenerator p}) : _).toRingHom.toAlgebra
  have hb : primePlusResidualTateBasis p hp ξ =
      (primePlusIntegralTateBasis p hp ξ).baseChange
        (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) :=
    primePlusResidualTateBasis_eq_baseChange p hp ξ
  have hmat : LinearMap.toMatrix' (D.integralAction g) =
      LinearMap.toMatrix' (primePlusIntegralTateCoordinateAction p hp ξ β g) := by
    apply Matrix.ext
    intro i j
    apply Subtype.ext
    exact (D.integral_spec g i j).trans
      (primePlusTateFieldCoordinateAction_integral_coeff p hp ξ β g i j).symm
  simpa only [hmat, hb, primePlusIntegralTateCoordinateAction_apply] using
    (primePlusIntegralCoordinateAction_residualMatrix p hp ξ β κ g).symm

/-- The residual character ratio of the selected plus Jacobian is the
canonical-prime cyclotomic character. The exact determinant of its completed
Tate factor is the explicit arithmetic premise. See
[TripathiGoswamiRevised, Proposition `primeresidual`]. -/
theorem primePlusSelectedTate_residualRatio
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    {E : Type*} [Field E] [ValuativeRel E]
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E]
    [FaithfulSMul (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E]
    (β : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[E])
    (κ : (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) ≃+*
      (𝒪[E] ⧸ 𝓂[E]))
    (hTateDet : ∀ g : AbsoluteGalois (realCyclotomicField p),
      letI := primePlusIntegralTateModule p hp ξ
      LinearMap.det ((primePlusIntegralTateRepresentation p hp ξ).baseChange E g) =
        algebraMap (AdicCompletion (Ideal.span {realPrimeGenerator p})
          (𝓞 (realCyclotomicField p))) E
          (TateModule.coefficientPrimeRingEquiv p
            (𝓞 (realCyclotomicField p))
            (Ideal.span {realPrimeGenerator p}) ((p - 1) / 2)
            (realPrimeRamification_pos p (by omega))
            (span_realPrimeGenerator_pow p (by omega))
              (PadicInt.toAdicCompletion p (𝓞 (realCyclotomicField p))
                (Field.cyclotomicCharacter (realCyclotomicField p) p g : ℤ_[p])))) :
    residualRatio (primePlusSelectedTateResidualData p hp ξ β κ hTateDet) =
      (Units.map κ.toMonoidHom).comp
        (realPrimeResidualCyclotomicCharacter
          (realCyclotomicField p) p (by omega)) := by
  let D := primePlusSelectedTateResidualData p hp ξ β κ hTateDet
  exact residualRatio_eq_primePlus_of_integralTateMatrix p hp ξ
    (primePlusTateFieldCoordinateAction p hp ξ β) D κ hTateDet
    (primePlusSelectedTateResidualMatrix p hp ξ β κ D)

/-- Irreducibility of the selected plus Jacobian's Tate action over its
coefficient field is absolute once complex conjugation has determinant `-1`.
The completed character value is obtained from its action on every `p`-power
root, not from the residual sign alone. See [TripathiGoswamiRevised,
Lemma `prime-absolute-irred`] and [GPRV, Theorem 10.1]. -/
theorem primePlusSelectedTate_absoluteIrreducible_of_involution
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    {E : Type*} [Field E] [ValuativeRel E]
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E]
    (β : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[E])
    (hβ : (inferInstance : Algebra (AdicCompletion
      (Ideal.span {realPrimeGenerator p}) (𝓞 (realCyclotomicField p))) E) =
      ((𝒪[E]).subtype.comp β).toAlgebra)
    (hTateDet : ∀ g : AbsoluteGalois (realCyclotomicField p),
      letI := primePlusIntegralTateModule p hp ξ
      LinearMap.det ((primePlusIntegralTateRepresentation p hp ξ).baseChange E g) =
        algebraMap (AdicCompletion (Ideal.span {realPrimeGenerator p})
          (𝓞 (realCyclotomicField p))) E
          (TateModule.coefficientPrimeRingEquiv p
            (𝓞 (realCyclotomicField p))
            (Ideal.span {realPrimeGenerator p}) ((p - 1) / 2)
            (realPrimeRamification_pos p (by omega))
            (span_realPrimeGenerator_pow p (by omega))
              (PadicInt.toAdicCompletion p (𝓞 (realCyclotomicField p))
                (Field.cyclotomicCharacter (realCyclotomicField p) p g : ℤ_[p]))))
    (hirred : (primePlusTateFieldCoordinateAction p hp ξ β).IsIrreducible)
    (h2 : (2 : E) ≠ 0)
    (ι : AlgebraicClosure (realCyclotomicField p) →+* ℂ)
    (c : AbsoluteGalois (realCyclotomicField p)) (hc : c ^ 2 = 1)
    (hconj : ∀ x, ι (c x) = star (ι x)) :
    (Representation.baseChange (AlgebraicClosure E)
      (primePlusTateFieldCoordinateAction p hp ξ β)).IsIrreducible := by
  let := primePlusIntegralTateModule p hp ξ
  have hcyclo :
      (Field.cyclotomicCharacter (realCyclotomicField p) p c : ℤ_[p]) = -1 := by
    exact cyclotomicCharacter.coe_eq_neg_one_of_complexConjugation
      p ι c.toRingEquiv hconj
  have hnative : LinearMap.det
      ((primePlusIntegralTateRepresentation p hp ξ).baseChange E c) = -1 := by
    rw [hTateDet c, hcyclo]
    simp
  cases hβ
  let : Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
    (𝓞 (realCyclotomicField p))) E := ((𝒪[E]).subtype.comp β).toAlgebra
  let := hirred
  apply Representation.isIrreducible_baseChange_of_involution
    (primePlusTateFieldCoordinateAction p hp ξ β) h2 c hc
  rw [primePlusTateFieldCoordinateAction_apply p hp ξ β c]
  exact (det_coordinateAction
    ((primePlusIntegralTateBasis p hp ξ).baseChange E)
    ((primePlusIntegralTateRepresentation p hp ξ).baseChange E c)).trans hnative

/-- Continuity of the selected Jacobian's field matrix follows from the
continuous native Tate action, the coordinates of its integral Tate basis, and
continuity of the coefficient specialization. -/
theorem primePlusTateFieldCoordinateAction_continuous
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [TopologicalSpace (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)))]
    (β : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[E])
    (hβ : Continuous ((𝒪[E]).subtype.comp β :
      AdicCompletion (Ideal.span {realPrimeGenerator p})
        (𝓞 (realCyclotomicField p)) → E))
    (hcoord : ∀ i : Fin 2,
      letI := primePlusIntegralTateModule p hp ξ
      Continuous (fun v : integralTate (realCyclotomicField p)
        (primePlusFiber p hp ξ).X p =>
        ((primePlusIntegralTateBasis p hp ξ).repr v) i))
    (i j : Fin 2) :
    Continuous (fun g : AbsoluteGalois (realCyclotomicField p) =>
      primePlusTateFieldCoordinateAction p hp ξ β g (Pi.single j 1) i) := by
  let := primePlusIntegralTateModule p hp ξ
  let α : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* E := (𝒪[E]).subtype.comp β
  have horbit (v : integralTate (realCyclotomicField p)
      (primePlusFiber p hp ξ).X p) :
      Continuous (fun g : AbsoluteGalois (realCyclotomicField p) =>
        primePlusIntegralTateRepresentation p hp ξ g v) := by
    have : Smooth (primePlusFamily p hp).X.hom :=
      (primePlusFamily_smoothOfRelativeDimension p hp).smooth
    have : IsProper (primePlusFiber p hp ξ).X.hom :=
      fiber_isProper (realCyclotomicField p) (primePlusFamily p hp)
        (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ)
    have : Smooth (primePlusFiber p hp ξ).X.hom :=
      fiber_smooth (realCyclotomicField p) (primePlusFamily p hp)
        (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ)
    have hnative := continuous_integralTateRepresentation
      (realCyclotomicField p) (primePlusFiber p hp ξ).X p
    have hpair : Continuous (fun g : AbsoluteGalois (realCyclotomicField p) =>
        (g, v)) := continuous_id.prodMk continuous_const
    have h := hnative.comp hpair
    exact h.congr (fun g =>
      (primePlusIntegralTateRepresentation_apply_native p hp ξ g v).symm)
  have hentry (g : AbsoluteGalois (realCyclotomicField p)) :
      primePlusTateFieldCoordinateAction p hp ξ β g (Pi.single j 1) i =
        α (((primePlusIntegralTateBasis p hp ξ).repr
          (primePlusIntegralTateRepresentation p hp ξ g
            ((primePlusIntegralTateBasis p hp ξ) j))) i) := by
    rw [primePlusTateFieldCoordinateAction_apply]
    exact coordinateAction_baseChange_entry
      (primePlusIntegralTateBasis p hp ξ)
      (primePlusIntegralTateRepresentation p hp ξ g) α i j
  have hcoordinate : Continuous (fun g : AbsoluteGalois (realCyclotomicField p) =>
      ((primePlusIntegralTateBasis p hp ξ).repr
        (primePlusIntegralTateRepresentation p hp ξ g
          ((primePlusIntegralTateBasis p hp ξ) j))) i) :=
    (hcoord i).comp (horbit ((primePlusIntegralTateBasis p hp ξ) j))
  have hfield := hβ.comp hcoordinate
  exact hfield.congr (fun g => (hentry g).symm)

/-- An abelian variety over a number field spreads out to an abelian scheme
outside finitely many finite places. The Néron–Ogg–Shafarevich criterion makes
its covariant `p`-adic Tate module unramified away from these places and those
above `p`. Here proper, smooth and geometrically connected are the
abelian-variety conditions on a commutative group scheme over a field. The
spreading-out step uses [src_stacks_spreading, Tags 01ZM, 0C0C, 081F]: descend
the scheme, group maps and identities, then smoothness and properness. Geometric
connectedness persists by the finite étale Stein factorization
[src_stacks_spreading, Tag 0E0D], whose generic degree is one. The local
criterion is [MilneAV, Chapter IV, §3, Theorem 3.5, printed p. 141]; its proof
identifies the unramified action on every prime-power torsion group, hence on
the integral inverse limit. The exceptional set also includes primes above `p`. -/
theorem abelianVariety_integralTate_unramifiedOutsideFinite
    (K : Type*) [Field K] [NumberField K]
    (A : CommGrp (Over (Spec (CommRingCat.of K))))
    [IsProper A.X.hom] [Smooth A.X.hom] [GeometricallyConnected A.X.hom]
    (p : ℕ) [Fact p.Prime] :
    ∃ ramified : Set (HeightOneSpectrum (𝓞 K)), ramified.Finite ∧
      ∀ q, q ∉ ramified →
        ∀ (P : Ideal (𝓞 K)) [P.IsMaximal], P = q.asIdeal →
        ∀ (Q : Ideal (𝓞 (AlgebraicClosure K))) [Q.IsMaximal] [Q.LiesOver P],
        ∀ g : AbsoluteGalois K,
          g ∈ Q.inertia (AbsoluteGalois K) →
            ∀ v : integralTate K A.X p,
              integralTateRepresentation K A.X p g v = v := by
  sorry

/-- Inertia triviality of the native Tate action passes to field coordinates
of the same selected plus Jacobian. -/
theorem primePlusTateFieldCoordinateAction_unramified_of_native
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    {E : Type*} [Field E] [ValuativeRel E]
    (β : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[E])
    (g : AbsoluteGalois (realCyclotomicField p))
    (h : ∀ v : integralTate (realCyclotomicField p)
      (primePlusFiber p hp ξ).X p,
      integralTateRepresentation (realCyclotomicField p)
        (primePlusFiber p hp ξ).X p g v = v) :
    primePlusTateFieldCoordinateAction p hp ξ β g = 1 := by
  let := primePlusIntegralTateModule p hp ξ
  have hnative : primePlusIntegralTateRepresentation p hp ξ g = 1 := by
    apply LinearMap.ext
    intro v
    rw [primePlusIntegralTateRepresentation_apply_native]
    exact h v
  let : Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E := ((𝒪[E]).subtype.comp β).toAlgebra
  rw [primePlusTateFieldCoordinateAction_apply]
  change ((primePlusIntegralTateBasis p hp ξ).baseChange E).equivFun.conjRingEquiv
    ((primePlusIntegralTateRepresentation p hp ξ g).baseChange E) = 1
  have hbase : (primePlusIntegralTateRepresentation p hp ξ g).baseChange E = 1 := by
    exact (congrArg (fun f => f.baseChange E) hnative).trans
      (LinearMap.baseChange_one _ _)
  exact (congrArg _ hbase).trans (map_one _)

/-- Good reduction outside finitely many places for the selected plus
Jacobian, transported through its chosen Tate basis. This uses the general
smooth proper group scheme input above and the selected family's admitted
properness, smoothness and geometric connectedness. -/
theorem primePlusTateFieldCoordinateAction_unramifiedOutsideFinite
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    {E : Type*} [Field E] [ValuativeRel E]
    (β : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[E]) :
    ∃ ramified : Set (HeightOneSpectrum (𝓞 (realCyclotomicField p))),
      ramified.Finite ∧
        ∀ q, q ∉ ramified →
          ∀ (P : Ideal (𝓞 (realCyclotomicField p))) [P.IsMaximal], P = q.asIdeal →
          ∀ (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p))))
            [Q.IsMaximal] [Q.LiesOver P],
          ∀ g : AbsoluteGalois (realCyclotomicField p),
            g ∈ Q.inertia (AbsoluteGalois (realCyclotomicField p)) →
              primePlusTateFieldCoordinateAction p hp ξ β g = 1 := by
  have : IsProper (primePlusFiber p hp ξ).X.hom :=
    fiber_isProper (realCyclotomicField p) (primePlusFamily p hp)
      (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ)
  have : Smooth (primePlusFiber p hp ξ).X.hom :=
    letI : Smooth (primePlusFamily p hp).X.hom :=
      (primePlusFamily_smoothOfRelativeDimension p hp).smooth
    fiber_smooth (realCyclotomicField p) (primePlusFamily p hp)
      (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ)
  have : GeometricallyConnected (primePlusFiber p hp ξ).X.hom :=
    fiber_geometricallyConnected (realCyclotomicField p) (primePlusFamily p hp)
      (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ)
  obtain ⟨ramified, hramified, hnative⟩ :=
    abelianVariety_integralTate_unramifiedOutsideFinite
      (realCyclotomicField p) (primePlusFiber p hp ξ) p
  refine ⟨ramified, hramified, ?_⟩
  intro q hq P _ hP Q _ _ g hg
  exact primePlusTateFieldCoordinateAction_unramified_of_native p hp ξ β g
    (hnative q hq P hP Q g hg)

private noncomputable def primePlusRamifiedSet
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    {E : Type*} [Field E] [ValuativeRel E]
    (β : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[E]) :
    Set (HeightOneSpectrum (𝓞 (realCyclotomicField p))) :=
  Classical.choose (primePlusTateFieldCoordinateAction_unramifiedOutsideFinite p hp ξ β)

private theorem primePlusRamifiedSet_finite
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    {E : Type*} [Field E] [ValuativeRel E]
    (β : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[E]) :
    (primePlusRamifiedSet p hp ξ β).Finite :=
  (Classical.choose_spec
    (primePlusTateFieldCoordinateAction_unramifiedOutsideFinite p hp ξ β)).1

private theorem primePlusRamifiedSet_unramified
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    {E : Type*} [Field E] [ValuativeRel E]
    (β : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[E]) :
    ∀ q, q ∉ primePlusRamifiedSet p hp ξ β →
      ∀ (P : Ideal (𝓞 (realCyclotomicField p))) [P.IsMaximal], P = q.asIdeal →
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p))))
        [Q.IsMaximal] [Q.LiesOver P],
      ∀ g : AbsoluteGalois (realCyclotomicField p),
        g ∈ Q.inertia (AbsoluteGalois (realCyclotomicField p)) →
          primePlusTateFieldCoordinateAction p hp ξ β g = 1 :=
  (Classical.choose_spec
    (primePlusTateFieldCoordinateAction_unramifiedOutsideFinite p hp ξ β)).2

/-- The selected Jacobian's Tate action supplies the residual matrix row for
the Skinner–Wiles checklist. Here `D` is any compatible residual datum; its
identification with the canonical-prime datum is a separate comparison. The
exact completed-Tate determinant, continuity, irreducibility, and local ordinary
comparisons remain explicit arithmetic inputs. Finite ramification follows
from the same Jacobian and the general input above. See
[TripathiGoswamiRevised, Proposition `SW-checklist`] and
[SkinnerWiles, §4.5, Theorem A]. -/
noncomputable def skinnerWilesWeightTwoInput_of_primePlusSelectedTate
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (E : Type*) [NormedField E] [ValuativeRel E]
    [Algebra ℚ_[p] E]
    [hPadicSmul : ContinuousSMul ℚ_[p] E]
    [IsUniformAddGroup E] [IsNonarchimedeanLocalField E]
    [CharP (𝒪[E] ⧸ 𝓂[E]) p]
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E]
    [FaithfulSMul (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E]
    (β : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[E])
    (hβ : (inferInstance : Algebra (AdicCompletion
      (Ideal.span {realPrimeGenerator p}) (𝓞 (realCyclotomicField p))) E) =
      ((𝒪[E]).subtype.comp β).toAlgebra)
    (κ : (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) ≃+*
      (𝒪[E] ⧸ 𝓂[E]))
    (hTateDet : ∀ g : AbsoluteGalois (realCyclotomicField p),
      letI := primePlusIntegralTateModule p hp ξ
      LinearMap.det ((primePlusIntegralTateRepresentation p hp ξ).baseChange E g) =
        algebraMap (AdicCompletion (Ideal.span {realPrimeGenerator p})
          (𝓞 (realCyclotomicField p))) E
          (TateModule.coefficientPrimeRingEquiv p
            (𝓞 (realCyclotomicField p))
            (Ideal.span {realPrimeGenerator p}) ((p - 1) / 2)
            (realPrimeRamification_pos p (by omega))
            (span_realPrimeGenerator_pow p (by omega))
              (PadicInt.toAdicCompletion p (𝓞 (realCyclotomicField p))
                (Field.cyclotomicCharacter (realCyclotomicField p) p g : ℤ_[p]))))
    (hcoeff : ∀ z : ℤ_[p],
      algebraMap (AdicCompletion (Ideal.span {realPrimeGenerator p})
        (𝓞 (realCyclotomicField p))) E
        (TateModule.coefficientPrimeRingEquiv p
          (𝓞 (realCyclotomicField p))
          (Ideal.span {realPrimeGenerator p}) ((p - 1) / 2)
          (realPrimeRamification_pos p (by omega))
          (span_realPrimeGenerator_pow p (by omega))
            (PadicInt.toAdicCompletion p (𝓞 (realCyclotomicField p)) z)) =
        algebraMap ℚ_[p] E (z : ℚ_[p]))
    (hirred : (primePlusTateFieldCoordinateAction p hp ξ β).IsIrreducible)
    (ι : AlgebraicClosure (realCyclotomicField p) →+* ℂ)
    (c : AbsoluteGalois (realCyclotomicField p)) (hc : c ^ 2 = 1)
    (hconj : ∀ x, ι (c x) = star (ι x))
    (D : SkinnerWilesResidualData (primePlusTateFieldCoordinateAction p hp ξ β))
    (hordinary : ∀ (P : Ideal (𝓞 (realCyclotomicField p))) [P.IsMaximal],
      (p : 𝓞 (realCyclotomicField p)) ∈ P →
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p))))
        [Q.IsMaximal] [Q.LiesOver P],
      SkinnerWilesOrdinaryAt p
        (primePlusTateFieldCoordinateAction p hp ξ β)
        D Q) :
    SkinnerWilesWeightTwoInput p
      (primePlusTateFieldCoordinateAction p hp ξ β) (cyclotomicField p) := by
  have h2 : (2 : E) ≠ 0 := by
    intro h
    have hmap : algebraMap ℚ_[p] E (2 : ℚ_[p]) =
        algebraMap ℚ_[p] E (0 : ℚ_[p]) := by
      simpa only [map_ofNat, map_zero] using h
    have hq : (2 : ℚ_[p]) = 0 := (algebraMap ℚ_[p] E).injective hmap
    norm_num at hq
  refine skinnerWilesWeightTwoInput_of_primePlusTateEquiv p hp ξ E
    (primePlusTateFieldCoordinateAction p hp ξ β)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ D κ ?_ ?_
  · exact primePlusTateFieldCoordinateEquiv p hp ξ β hβ
  · exact hTateDet
  · exact hcoeff
  · infer_instance
  · let : ContinuousSMul ℚ_[p] E := hPadicSmul
    have h₁ : Continuous (fun x : ℤ_[p] × E => (x.1 : ℚ_[p])) :=
      continuous_subtype_val.comp continuous_fst
    have h₂ : Continuous (fun x : ℤ_[p] × E => x.2) := continuous_snd
    have h : Continuous (fun x : ℤ_[p] × E => (x.1 : ℚ_[p]) • x.2) :=
      h₁.smul h₂
    let : Algebra ℤ_[p] E :=
      ((algebraMap ℚ_[p] E).comp (algebraMap ℤ_[p] ℚ_[p])).toAlgebra
    have hsmul (z : ℤ_[p]) (a : E) : z • a = (z : ℚ_[p]) • a := by
      simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra,
        RingHom.comp_apply]
      rfl
    let : ContinuousSMul ℤ_[p] E := ⟨by
      exact h.congr (fun x => (hsmul x.1 x.2).symm)⟩
    intro i j
    apply primePlusTateFieldCoordinateAction_continuous_of_padicScalars
      p hp ξ β
    intro z
    have hz := hcoeff z
    cases hβ
    simpa only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply,
      PadicInt.algebraMap_apply] using hz
  · exact primePlusSelectedTate_absoluteIrreducible_of_involution
      p hp ξ β hβ hTateDet hirred h2 ι c hc hconj
  · exact primePlusRamifiedSet p hp ξ β
  · exact primePlusRamifiedSet_finite p hp ξ β
  · exact primePlusRamifiedSet_unramified p hp ξ β
  · exact primePlusSelectedTateResidualMatrix p hp ξ β κ D
  · exact hordinary

/-- The residual datum of the actual selected Jacobian, obtained from the
native completed Tate determinant through an operator-level comparison with
its chosen integral lattice. Its fixed line comes from that Jacobian's
canonical-prime torsion point. See [TripathiGoswamiRevised, Lemma
`RMtorsion` and Proposition `primeresidual`]. -/
noncomputable def primePlusNativeComparedTateResidualData
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    {E : Type*} [Field E] [ValuativeRel E]
    [Algebra ℚ_[p] E]
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E]
    [FaithfulSMul (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E]
    (β : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[E])
    (κ : (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) ≃+*
      (𝒪[E] ⧸ 𝓂[E]))
    (τ : RealPrimePowerCompletion p 0 →ₐ[ℚ_[p]] E)
    (e : letI := primePlusIntegralTateModule p hp ξ
      letI : Algebra (RealPrimePowerCompletion p 0) E := τ.toAlgebra
      ((primePlusLocalTateRepresentation p hp ξ).ρ.baseChange E).Equiv
        ((primePlusIntegralTateRepresentation p hp ξ).baseChange E))
    (hcoeff : ∀ z : ℤ_[p],
      algebraMap (AdicCompletion (Ideal.span {realPrimeGenerator p})
        (𝓞 (realCyclotomicField p))) E
        (TateModule.coefficientPrimeRingEquiv p
          (𝓞 (realCyclotomicField p))
          (Ideal.span {realPrimeGenerator p}) ((p - 1) / 2)
          (realPrimeRamification_pos p (by omega))
          (span_realPrimeGenerator_pow p (by omega))
            (PadicInt.toAdicCompletion p (𝓞 (realCyclotomicField p)) z)) =
        algebraMap ℚ_[p] E (z : ℚ_[p])) :
    SkinnerWilesResidualData (primePlusTateFieldCoordinateAction p hp ξ β) :=
  primePlusSelectedTateResidualData p hp ξ β κ
    (primePlusIntegralTate_det_of_nativeComparison p hp ξ E τ e hcoeff)

/-- The native determinant comparison preserves the selected fixed-vector
ordering: the second residual character is the trivial one. -/
theorem primePlusNativeComparedTateResidualData_chi₂_eq_one
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    {E : Type*} [Field E] [ValuativeRel E]
    [Algebra ℚ_[p] E]
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E]
    [FaithfulSMul (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E]
    (β : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[E])
    (κ : (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) ≃+*
      (𝒪[E] ⧸ 𝓂[E]))
    (τ : RealPrimePowerCompletion p 0 →ₐ[ℚ_[p]] E)
    (e : letI := primePlusIntegralTateModule p hp ξ
      letI : Algebra (RealPrimePowerCompletion p 0) E := τ.toAlgebra
      ((primePlusLocalTateRepresentation p hp ξ).ρ.baseChange E).Equiv
        ((primePlusIntegralTateRepresentation p hp ξ).baseChange E))
    (hcoeff : ∀ z : ℤ_[p],
      algebraMap (AdicCompletion (Ideal.span {realPrimeGenerator p})
        (𝓞 (realCyclotomicField p))) E
        (TateModule.coefficientPrimeRingEquiv p
          (𝓞 (realCyclotomicField p))
          (Ideal.span {realPrimeGenerator p}) ((p - 1) / 2)
          (realPrimeRamification_pos p (by omega))
          (span_realPrimeGenerator_pow p (by omega))
            (PadicInt.toAdicCompletion p (𝓞 (realCyclotomicField p)) z)) =
        algebraMap ℚ_[p] E (z : ℚ_[p])) :
    (primePlusNativeComparedTateResidualData p hp ξ β κ τ e hcoeff).chi₂ = 1 := by
  unfold primePlusNativeComparedTateResidualData
  exact primePlusSelectedTateResidualData_chi₂_eq_one p hp ξ β κ
    (primePlusIntegralTate_det_of_nativeComparison p hp ξ E τ e hcoeff)

/-- The residual ratio of the selected datum constructed from the native
completed determinant is the canonical-prime cyclotomic character. -/
theorem primePlusNativeComparedTate_residualRatio
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    {E : Type*} [Field E] [ValuativeRel E] [Algebra ℚ_[p] E]
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E]
    [FaithfulSMul (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E]
    (β : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[E])
    (κ : (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) ≃+*
      (𝒪[E] ⧸ 𝓂[E]))
    (τ : RealPrimePowerCompletion p 0 →ₐ[ℚ_[p]] E)
    (e : letI := primePlusIntegralTateModule p hp ξ
      letI : Algebra (RealPrimePowerCompletion p 0) E := τ.toAlgebra
      ((primePlusLocalTateRepresentation p hp ξ).ρ.baseChange E).Equiv
        ((primePlusIntegralTateRepresentation p hp ξ).baseChange E))
    (hcoeff : ∀ z : ℤ_[p],
      algebraMap (AdicCompletion (Ideal.span {realPrimeGenerator p})
        (𝓞 (realCyclotomicField p))) E
        (TateModule.coefficientPrimeRingEquiv p
          (𝓞 (realCyclotomicField p))
          (Ideal.span {realPrimeGenerator p}) ((p - 1) / 2)
          (realPrimeRamification_pos p (by omega))
          (span_realPrimeGenerator_pow p (by omega))
            (PadicInt.toAdicCompletion p (𝓞 (realCyclotomicField p)) z)) =
        algebraMap ℚ_[p] E (z : ℚ_[p])) :
    residualRatio (primePlusNativeComparedTateResidualData p hp ξ β κ τ e hcoeff) =
      (Units.map κ.toMonoidHom).comp
        (realPrimeResidualCyclotomicCharacter
          (realCyclotomicField p) p (by omega)) := by
  exact primePlusSelectedTate_residualRatio p hp ξ β κ
    (primePlusIntegralTate_det_of_nativeComparison p hp ξ E τ e hcoeff)

end HilbertModularity.Hypergeometric
