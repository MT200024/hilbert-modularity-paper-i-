/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.TateModule.GoodReductionLabelledPolynomial
public import HilbertModularity.Geometry.TateModule.CoefficientIsomorphism
public import HilbertModularity.RepresentationTheory.CompatiblePolynomials
public import HilbertModularity.Geometry.GroupScheme.Isomorphism
public import HilbertModularity.Geometry.TateModule.RealMultiplicationPairing

/-! # Fixed coefficient labels on a good-reduction model

Transport the integral endomorphism action along an actual group-scheme
isomorphism. The induced Tate equivalence keeps the coefficient embedding fixed,
as required in [TripathiGoswamiRevised, Lemma `labelled-RM-compat`].
-/

public section
noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj NumberField TensorProduct

namespace AlgebraicGeometry.GroupScheme

universe u

variable (K : Type u) [Field K]
  {A B : CommGrp (Over (Spec (CommRingCat.of K)))}

/-- Conjugate actual algebraic endomorphisms to an isomorphic group scheme. -/
def transportEndomorphism (e : A ≅ B) : End A →+* End B where
  toFun f := e.inv ≫ f ≫ e.hom
  map_one' := by simp only [End.one_def, Category.id_comp, Iso.inv_hom_id]
  map_mul' f g := by simp only [End.mul_def, Category.assoc, Iso.hom_inv_id_assoc]
  map_zero' := by exact (congrArg (e.inv ≫ ·) (Limits.zero_comp : (0 : A ⟶ A) ≫ e.hom = 0)).trans Limits.comp_zero
  map_add' f g := by
    change e.inv ≫ (f + g) ≫ e.hom =
      e.inv ≫ f ≫ e.hom + e.inv ≫ g ≫ e.hom
    exact (congrArg (e.inv ≫ ·) (Preadditive.add_comp A A B f g e.hom)).trans
      (Preadditive.comp_add B A B e.inv (f ≫ e.hom) (g ≫ e.hom))

/-- The original and transported coefficient actions intertwine on geometric points. -/
theorem pointsEndomorphism_transport (E : Type u) [Field E] [Algebra K E]
    (e : A ≅ B) (f : End A) (x : Points K E A.X) :
    pointsMap K E e.hom.hom.hom.hom (pointsEndomorphismMap K E A f x) =
      pointsEndomorphismMap K E B (transportEndomorphism K e f)
        (pointsMap K E e.hom.hom.hom.hom x) := by
  have h : f ≫ e.hom = e.hom ≫ transportEndomorphism K e f := by
    simp only [transportEndomorphism,
      RingHom.coe_mk,
      MonoidHom.coe_mk,
      OneHom.coe_mk,
      Iso.hom_inv_id_assoc]
  have hh := congrArg (fun z : A ⟶ B => z.hom.hom.hom) h
  simp only [CommGrp.comp_hom, Grp.comp_hom_hom] at hh
  change (x.toMul ≫ f.hom.hom.hom) ≫ e.hom.hom.hom.hom =
    (x.toMul ≫ e.hom.hom.hom.hom) ≫ (transportEndomorphism K e f).hom.hom.hom
  rw [Category.assoc, hh, Category.assoc]

variable [NumberField K]
  (P : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
  (M : CommGrp (Over (Spec (CommRingCat.of (P.valuationSubringAtPrime K)))))
  [IsProper M.X.hom] [Smooth M.X.hom] [GeometricallyConnected M.X.hom]

/-- The fixed-labelled representation on the original variety agrees with the
same label on its good-reduction model. The model action is constructed from
the given integral RM action, not postulated independently. -/
def goodReductionLabelledTateEquiv
    (e : A ≅ localGenericFiber K P M)
    (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [NumberField F]
    (φ : 𝓞 F →+* End A)
    (L : Type*) [Field L] [Algebra ℚ_[p] L] [Algebra ℚ L]
    (hL : ∀ a : F, ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (σ : F →ₐ[ℚ] L) :
    (labelledTateSubrepresentation K A.X p F L hL
      ((pointsEndomorphismMap K (AlgebraicClosure K) A).comp φ)
      (pointsEndomorphismAction_realized K A F φ) σ).toRepresentation.Equiv
    (labelledTateSubrepresentation K (localGenericFiber K P M).X p F L hL
      (fiberPointsAction K (AlgebraicClosure K) M (localGenericPoint K P) (𝓞 F)
        (extendLocalGenericAction K P M ((transportEndomorphism K e).comp φ)))
      (fiberPointsAction_realized K (AlgebraicClosure K) M (localGenericPoint K P)
        (𝓞 F) (extendLocalGenericAction K P M ((transportEndomorphism K e).comp φ)))
      σ).toRepresentation := by
  let e' : A.X ≅ (localGenericFiber K P M).X := (CommGrp.forget _).mapIso e
  letI : IsMonHom e'.hom := inferInstanceAs (IsMonHom e.hom.hom.hom.hom)
  letI : IsMonHom e'.inv := inferInstanceAs (IsMonHom e.inv.hom.hom.hom)
  refine labelledTateEquiv K p F L hL _ _ e' ?_ _ _ σ
  intro a x
  rw [fiberPointsAction_extendLocalGenericAction]
  exact pointsEndomorphism_transport K (AlgebraicClosure K) e (φ a) x

/-- One algebraic polynomial computes geometric Frobenius on the original
fixed-labelled cohomological factor at good reduction, uniformly in the auxiliary
prime. A generic-fibre isomorphism transports the given RM action to the model. -/
theorem exists_labelled_dual_frobeniusPolynomial_of_goodReduction
    (K : Type u) [Field K] [NumberField K]
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (B : CommGrp (Over (Spec (CommRingCat.of (P.valuationSubringAtPrime K)))))
    [IsProper B.X.hom] [Smooth B.X.hom] [GeometricallyConnected B.X.hom]
    (A : CommGrp (Over (Spec (CommRingCat.of K))))
    (e : A ≅ localGenericFiber K P B)
    (F : Type*) [Field F] [NumberField F] (φ : 𝓞 F →+* End A)
    (E : Type*) [Field E] [CharZero E] [Algebra ℚ E]
    (hE : ∀ x : F, ((minpoly ℚ x).map (algebraMap ℚ E)).Splits)
    (σ : F →ₐ[ℚ] E) :
    ∃ R : Polynomial E,
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure K))) [Q.IsMaximal] [Q.LiesOver P.asIdeal]
        (p : ℕ) (hp : p.Prime) (_ : (p : 𝓞 K) ∉ P.asIdeal),
        letI : Fact p.Prime := ⟨hp⟩
        ∀ (_ : FiniteDimensional ℚ_[p] (rationalTate K A.X p))
          (L : Type*) [Field L] [CharZero L] [Algebra ℚ_[p] L] [Algebra ℚ L]
          [IsScalarTower ℚ ℚ_[p] L]
          (hL : ∀ x : F, ((minpoly ℚ x).map (algebraMap ℚ L)).Splits)
          (j : E →ₐ[ℚ] L)
          (basis : Module.Basis (Fin 2) L
            (labelledTateSubrepresentation K A.X p F L hL
              ((pointsEndomorphismMap K (AlgebraicClosure K) A).comp φ)
              (pointsEndomorphismAction_realized K A F φ) (j.comp σ)).toSubmodule),
          letI := Module.Finite.of_basis basis
          letI := Module.Free.of_basis basis
          letI := Module.Finite.of_basis basis.dualBasis
          letI : Module.Free L
            (Module.Dual L (labelledTateSubrepresentation K A.X p F L hL
              ((pointsEndomorphismMap K (AlgebraicClosure K) A).comp φ)
              (pointsEndomorphismAction_realized K A F φ) (j.comp σ)).toSubmodule) := Module.Free.of_divisionRing _ _
          ((labelledTateSubrepresentation K A.X p F L hL
            ((pointsEndomorphismMap K (AlgebraicClosure K) A).comp φ)
            (pointsEndomorphismAction_realized K A F φ) (j.comp σ)).toRepresentation.dual
                (NumberField.arithmeticFrobenius K (AlgebraicClosure K) P.asIdeal Q)⁻¹).charpoly =
            R.map j.toRingHom := by
  classical
  let ψ : 𝓞 F →+* End (localGenericFiber K P B) := (transportEndomorphism K e).comp φ
  have h := exists_goodReduction_labelled_dual_frobeniusPolynomial K P B F ψ E hE σ
  obtain ⟨R, hR⟩ := h
  refine ⟨R, ?_⟩
  intro Q _ _ p hp hpP
  let : Fact p.Prime := ⟨hp⟩
  intro hfinite L _ _ _ _ _ hL j basis
  let := hfinite
  let te := tateEquiv K p e
  let := te.toLinearEquiv.finiteDimensional
  let c := goodReductionLabelledTateEquiv K P B e p F φ L hL (j.comp σ)
  let modelBasis := basis.map c.toLinearEquiv
  let := Module.Finite.of_basis basis
  let := Module.Free.of_basis basis
  let := Module.Finite.of_basis modelBasis
  let := Module.Free.of_basis modelBasis
  let := Module.Finite.of_basis basis.dualBasis
  let := Module.Finite.of_basis modelBasis.dualBasis
  with_reducible
    let cd := HilbertModularity.representationDualEquiv (K := L)
      (V := (labelledTateSubrepresentation K A.X p F L hL
        ((pointsEndomorphismMap K (AlgebraicClosure K) A).comp φ)
        (pointsEndomorphismAction_realized K A F φ) (j.comp σ)).toSubmodule)
      (W := (labelledTateSubrepresentation K (localGenericFiber K P B).X p F L hL
        (fiberPointsAction K (AlgebraicClosure K) B (localGenericPoint K P) (𝓞 F)
          (extendLocalGenericAction K P B ψ))
        (fiberPointsAction_realized K (AlgebraicClosure K) B (localGenericPoint K P)
          (𝓞 F) (extendLocalGenericAction K P B ψ)) (j.comp σ)).toSubmodule)
      (G := AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) c
    have hc := Representation.Equiv.charpoly_eq (K := L) cd
      (NumberField.arithmeticFrobenius K (AlgebraicClosure K) P.asIdeal Q)⁻¹
    have hm := hR Q p hp hpP inferInstance L hL j modelBasis
    exact hc.trans hm

end AlgebraicGeometry.GroupScheme
