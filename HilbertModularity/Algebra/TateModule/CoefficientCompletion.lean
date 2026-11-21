/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Algebra.TateModule.PrincipalReduction
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.Algebra.Module.TransferInstance

/-! # Completed integral coefficients on Tate modules

The actual compatible-family Tate module is complete for the `p`-adic
filtration induced by any coefficient action. The diagonal of a compatible
sequence of Tate vectors constructs its limit. Consequently its coefficient
action extends to the native adic completion of the coefficient ring.
See [TripathiGoswami, integral RM-prime Tate lattice].
-/

@[expose] public noncomputable section

namespace TateModule

attribute [local instance] coefficientModule

variable (p : ℕ) [Fact p.Prime] (R A : Type*) [CommRing R] [AddCommGroup A] [Module R A]

/-- The coefficient-ideal filtration is the actual finite-projection kernel filtration. -/
theorem mem_coefficient_pow_smul_top_iff (n : ℕ) (x : integral p A) :
    x ∈ ((Ideal.span {(p : R)}) ^ n • (⊤ : Submodule R (integral p A))) ↔
      projection p A n x = 0 := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists, projection_eq_zero_iff]
  simp only [Submodule.mem_top, true_and, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]

/-- Coefficient congruence is equality at the corresponding actual torsion level. -/
theorem coefficient_smodEq_iff_projection_eq (n : ℕ) (x y : integral p A) :
    x ≡ y [SMOD ((Ideal.span {(p : R)}) ^ n • (⊤ : Submodule R (integral p A)))] ↔
      projection p A n x = projection p A n y := by
  rw [SModEq.sub_mem, mem_coefficient_pow_smul_top_iff, map_sub, sub_eq_zero]

/-- The actual Tate inverse limit is complete over its integral coefficient ring at `p`. -/
instance coefficientIsAdicComplete :
    IsAdicComplete (Ideal.span {(p : R)}) (integral p A) where
  haus' x hx := by
    apply Subtype.ext
    funext n
    have h := (coefficient_smodEq_iff_projection_eq p R A n x 0).mp (hx n)
    change projection p A n x = projection p A n 0
    exact h
  prec' f hf := by
    have hproj {m n : ℕ} (hmn : m ≤ n) :
        projection p A m (f m) = projection p A m (f n) :=
      (coefficient_smodEq_iff_projection_eq p R A m (f m) (f n)).mp (hf hmn)
    let x : integral p A := ⟨fun n => (f n).val n, by
      intro n
      change transition p A n (projection p A (n + 1) (f (n + 1))) = projection p A n (f n)
      rw [transition_projection]
      exact (hproj (Nat.le_succ n)).symm⟩
    refine ⟨x, fun n => (coefficient_smodEq_iff_projection_eq p R A n (f n) x).mpr ?_⟩
    rfl

/-- The completed coefficient ring acts on the original Tate module via its actual completeness. -/
local instance completedCoefficientModule :
    Module (AdicCompletion (Ideal.span {(p : R)}) R) (integral p A) :=
  (AdicCompletion.ofLinearEquiv (Ideal.span {(p : R)}) (integral p A)).toAddEquiv.module _

/-- The completed action extends the original integral coefficient action. -/
local instance completedCoefficientScalarTower :
    IsScalarTower R (AdicCompletion (Ideal.span {(p : R)}) R) (integral p A) :=
  (AdicCompletion.ofLinearEquiv (Ideal.span {(p : R)}) (integral p A)).isScalarTower _

@[simp]
theorem completedCoefficient_smul_algebraMap (r : R) (x : integral p A) :
    algebraMap R (AdicCompletion (Ideal.span {(p : R)}) R) r • x = r • x :=
  algebraMap_smul _ r x

/-- Completion transports actual Tate vectors linearly over the completed coefficient ring. -/
def coefficientCompletionEquiv :
    integral p A ≃ₗ[AdicCompletion (Ideal.span {(p : R)}) R]
      AdicCompletion (Ideal.span {(p : R)}) (integral p A) :=
  (AdicCompletion.ofLinearEquiv (Ideal.span {(p : R)}) (integral p A)).toAddEquiv.linearEquiv _

@[simp]
theorem coefficientCompletionEquiv_apply (x : integral p A) :
    coefficientCompletionEquiv p R A x =
      AdicCompletion.of (Ideal.span {(p : R)}) (integral p A) x := rfl

/-- An endomorphism of the actual Tate module extends linearly to completed coefficients. -/
def completedCoefficientLinearMap (f : integral p A →ₗ[R] integral p A) :
    integral p A →ₗ[AdicCompletion (Ideal.span {(p : R)}) R] integral p A :=
  (coefficientCompletionEquiv p R A).symm.toLinearMap ∘ₗ
    AdicCompletion.map (Ideal.span {(p : R)}) f ∘ₗ
      (coefficientCompletionEquiv p R A).toLinearMap

@[simp]
theorem completedCoefficientLinearMap_apply (f : integral p A →ₗ[R] integral p A)
    (x : integral p A) : completedCoefficientLinearMap p R A f x = f x := by
  apply (coefficientCompletionEquiv p R A).injective
  change coefficientCompletionEquiv p R A
    ((coefficientCompletionEquiv p R A).symm
      (AdicCompletion.map (Ideal.span {(p : R)}) f (coefficientCompletionEquiv p R A x))) = _
  rw [LinearEquiv.apply_symm_apply, coefficientCompletionEquiv_apply,
    coefficientCompletionEquiv_apply, AdicCompletion.map_of]

omit [Fact p.Prime] in
/-- Every completed coefficient differs from an original coefficient by a multiple of `p`. -/
theorem exists_completedCoefficient_sub_algebraMap
    (c : AdicCompletion (Ideal.span {(p : R)}) R) :
    ∃ r : R, ∃ d : AdicCompletion (Ideal.span {(p : R)}) R,
      c = algebraMap R _ r + algebraMap R _ (p : R) * d := by
  let I : Ideal R := Ideal.span {(p : R)}
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalOneₐ I c)
  have hc : c - algebraMap R (AdicCompletion I R) r ∈
      RingHom.ker (AdicCompletion.evalOneₐ I).toRingHom := by
    change AdicCompletion.evalOneₐ I (c - algebraMap R (AdicCompletion I R) r) = 0
    rw [map_sub, AlgHom.commutes]
    change AdicCompletion.evalOneₐ I c - Ideal.Quotient.mk I r = 0
    rw [hr, sub_self]
  rw [AdicCompletion.ker_evalOneₐ_eq_map I (Submodule.fg_span_singleton _)] at hc
  change c - algebraMap R (AdicCompletion I R) r ∈
    (Ideal.span {(p : R)}).map (algebraMap R (AdicCompletion I R)) at hc
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton] at hc
  obtain ⟨d, hd⟩ := hc
  exact ⟨r, d, by rw [← hd, add_comm, sub_add_cancel]⟩

omit [Fact p.Prime] in
/-- Reduction of completed coefficients at a principal divisor of `p`. -/
def completedPrincipalResidue (a b : R) (hab : a * b = (p : R)) :
    AdicCompletion (Ideal.span {(p : R)}) R →+* R ⧸ Ideal.span {a} :=
  (Ideal.Quotient.factor (show Ideal.span {(p : R)} ≤ Ideal.span {a} from by
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton]
    exact ⟨b, hab.symm⟩)).comp (AdicCompletion.evalOneₐ (Ideal.span {(p : R)})).toRingHom

omit [Fact p.Prime] in
@[simp]
theorem completedPrincipalResidue_algebraMap (a b : R) (hab : a * b = (p : R)) (r : R) :
    completedPrincipalResidue p R a b hab (algebraMap R _ r) =
      Ideal.Quotient.mk (Ideal.span {a}) r := rfl

/-- The principal Tate projection respects the canonical residue of completed coefficients. -/
theorem principalProjection_completed_smul (a b : R) (hab : a * b = (p : R))
    (c : AdicCompletion (Ideal.span {(p : R)}) R) (x : integral p A) :
    principalProjection p R A a b hab (c • x) =
      completedPrincipalResidue p R a b hab c • principalProjection p R A a b hab x := by
  obtain ⟨r, d, rfl⟩ := exists_completedCoefficient_sub_algebraMap p R c
  have hpzero : Ideal.Quotient.mk (Ideal.span {a}) (p : R) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [Ideal.mem_span_singleton]
    exact ⟨b, hab.symm⟩
  have hz (y : integral p A) : principalProjection p R A a b hab ((p : R) • y) = 0 := by
    rw [map_smul, ← hab, mul_comm a b, mul_smul]
    have ha : a • principalProjection p R A a b hab y = 0 :=
      Subtype.ext (principalProjection p R A a b hab y).property
    rw [ha, smul_zero]
  rw [add_smul, mul_smul, completedCoefficient_smul_algebraMap,
    completedCoefficient_smul_algebraMap, map_add, hz, add_zero, map_smul]
  rw [map_add, map_mul, completedPrincipalResidue_algebraMap,
    completedPrincipalResidue_algebraMap, hpzero, zero_mul, add_zero]
  rfl

omit [Fact p.Prime] in
/-- The completed principal residue map is onto the original coefficient residue ring. -/
theorem completedPrincipalResidue_surjective (a b : R) (hab : a * b = (p : R)) :
    Function.Surjective (completedPrincipalResidue p R a b hab) := by
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨algebraMap R _ r, completedPrincipalResidue_algebraMap p R a b hab r⟩

omit [Fact p.Prime] in
/-- Completion does not change the principal residue ideal or its residue ring. -/
theorem ker_completedPrincipalResidue (a b : R) (hab : a * b = (p : R)) :
    RingHom.ker (completedPrincipalResidue p R a b hab) =
      Ideal.span {algebraMap R (AdicCompletion (Ideal.span {(p : R)}) R) a} := by
  ext c
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  have ha : completedPrincipalResidue p R a b hab (algebraMap R _ a) = 0 := by
    rw [completedPrincipalResidue_algebraMap]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton a))
  have hp : algebraMap R (AdicCompletion (Ideal.span {(p : R)}) R) (p : R) =
      algebraMap R _ a * algebraMap R _ b := by rw [← map_mul, hab]
  constructor
  · intro hc
    obtain ⟨r, d, hd⟩ := exists_completedCoefficient_sub_algebraMap p R c
    have hr : Ideal.Quotient.mk (Ideal.span {a}) r = 0 := by
      rw [hd, hp, map_add, map_mul, map_mul, ha, zero_mul, zero_mul,
        add_zero, completedPrincipalResidue_algebraMap] at hc
      exact hc
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hr)
    refine ⟨algebraMap R _ t + algebraMap R _ b * d, ?_⟩
    rw [hd, ht, hp, map_mul, mul_add, mul_assoc]
  · rintro ⟨d, rfl⟩
    rw [map_mul, ha, zero_mul]

omit [Fact p.Prime] in
/-- The actual residue field of a principal coefficient prime is unchanged by completion at `p`. -/
def completedPrincipalResidueEquiv (a b : R) (hab : a * b = (p : R)) :
    (AdicCompletion (Ideal.span {(p : R)}) R ⧸
      Ideal.span {algebraMap R (AdicCompletion (Ideal.span {(p : R)}) R) a}) ≃+*
      R ⧸ Ideal.span {a} :=
  (Ideal.quotEquivOfEq (ker_completedPrincipalResidue p R a b hab).symm).trans
    (RingHom.quotientKerEquivOfSurjective (completedPrincipalResidue_surjective p R a b hab))

end TateModule
