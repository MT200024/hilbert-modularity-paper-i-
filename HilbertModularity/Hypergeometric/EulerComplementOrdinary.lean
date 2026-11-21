/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.ChosenEulerComplement
public import HilbertModularity.NumberTheory.LocalGlobalInertia
public import HilbertModularity.RepresentationTheory.FiniteCharacterTwist
public import HilbertModularity.RepresentationTheory.WeightZeroQuotient
public import HilbertModularity.RepresentationTheory.Duality

/-! # The ordinary quotient under the chosen Euler complement

The quadratic comparison character is selected for one coefficient
realization before the parameter. Its restriction to an actual local Galois
group is finite, so the existing finite-character period theorem preserves
the selected rank-one weight-zero quotient at complementary fibres.
-/

public noncomputable section

open AlgebraicGeometry IsDedekindDomain NumberField.LocalGalois
open HilbertModularity.Cyclotomic
open scoped NumberField TensorProduct

namespace HilbertModularity.Hypergeometric

attribute [local instance] completionPadicAlgebra completionPadicTower
  completionComplexAlgebra completionComplexTower completionComplexRationalTower

private theorem characterTensor_comp
    {E G H V : Type*} [Field E] [Group G] [Group H]
    [AddCommGroup V] [Module E V]
    (ρ : Representation E G V) (χ : G →* Eˣ) (s : H →* G) :
    (((Representation.ofCharacter χ).tprod ρ).comp s) =
      ((Representation.ofCharacter (χ.comp s)).tprod (ρ.comp s)) := by
  rfl

/-- Dualizing a scalar character twist inverts the character on the same
actual dual carrier. -/
private def dualCharacterTwistEquiv
    {E G V : Type*} [Field E] [Group G]
    [AddCommGroup V] [Module E V]
    (ρ : Representation E G V) (χ : G →* Eˣ) :
    ((ρ.characterTwist χ).dual).Equiv
      (ρ.dual.characterTwist χ⁻¹) :=
  .mk (LinearEquiv.refl E (Module.Dual E V)) (by
    intro g
    apply LinearMap.ext
    intro φ
    apply LinearMap.ext
    intro v
    change φ ((χ g⁻¹ : E) • ρ g⁻¹ v) =
      ((χ⁻¹ g : E) • (ρ.dual g φ)) v
    have hχ : (χ g⁻¹ : E) = (χ⁻¹ g : E) := by simp
    rw [hχ, map_smul]
    rfl)

/-- A quadratic comparison on the effective cohomological action gives
the same finite twist on its actual covariant dual. In general duality
uses the inverse character; quadraticity identifies that inverse here. -/
private def quadraticDualTensorEquiv
    {E G V U : Type*} [Field E] [Group G]
    [AddCommGroup V] [Module E V] [AddCommGroup U] [Module E U]
    (ρ : Representation E G V) (σ : Representation E G U)
    (χ : G →* Eˣ) (hχ2 : χ ^ 2 = 1)
    (e : ((Representation.ofCharacter χ).tprod ρ).Equiv σ) :
    ((Representation.ofCharacter χ).tprod ρ.dual).Equiv σ.dual := by
  have hmul : χ * χ = 1 := by simpa only [pow_two] using hχ2
  have hχinv : χ⁻¹ = χ := by
    apply MonoidHom.ext
    intro g
    have hg : χ g * χ g = (1 : Eˣ) := by
      have h := congrArg (fun f : G →* Eˣ => f g) hmul
      simpa only [MonoidHom.mul_apply, MonoidHom.one_apply] using h
    calc
      (χ⁻¹) g = (χ g)⁻¹ := rfl
      _ = (χ g)⁻¹ * (χ g * χ g) := by rw [hg, mul_one]
      _ = χ g := by group
  let eTw := (ρ.characterTwistTensorEquiv χ).symm.trans e
  let eD := HilbertModularity.representationDualEquiv eTw
  have eInv : ((Representation.ofCharacter χ⁻¹).tprod ρ.dual).Equiv σ.dual :=
    (ρ.dual.characterTwistTensorEquiv χ⁻¹).trans
      ((dualCharacterTwistEquiv ρ χ).symm.trans eD)
  simpa only [hχinv] using eInv

private theorem weightZeroQuotient_of_equiv
    (p : ℕ) [Fact p.Prime]
    {K E G V U : Type*} [Field K] [Field E]
    [Algebra ℚ_[p] K] [Algebra ℚ_[p] E]
    [Algebra K ℂ_[p]] [IsScalarTower ℚ_[p] K ℂ_[p]]
    [Group G] [AddCommGroup V] [Module E V] [Module ℚ_[p] V]
    [IsScalarTower ℚ_[p] E V]
    [AddCommGroup U] [Module E U] [Module ℚ_[p] U]
    [IsScalarTower ℚ_[p] E U]
    (ι : G →* (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p))
    (hK : ∀ (g : G) (a : K), PadicComplex.galoisEquiv p (ι g)
      (algebraMap K ℂ_[p] a) = algebraMap K ℂ_[p] a)
    {ρ : Representation E G V} {τ : Representation E G U}
    (e : ρ.Equiv τ)
    (W : HodgeTate.WeightZeroQuotient p ι hK ρ) :
    Nonempty (HodgeTate.WeightZeroQuotient p ι hK τ) := by
  let S := e.subrepresentationOrderIso W.kernel
  let qEq := e.quotientCongr W.kernel
  have hdim : Module.finrank E (U ⧸ S.toSubmodule) = 1 :=
    qEq.toLinearEquiv.finrank_eq.symm.trans W.finrank_eq_one
  have hcomp : Function.Bijective (HodgeTate.comparison p ι hK
      ((τ.quotient S.toSubmodule S.apply_mem_toSubmodule).restrictScalars ℚ_[p])) :=
    (HodgeTate.comparison_bijective_iff p ι hK
      (qEq.restrictScalars ℚ_[p])).mp W.comparison_bijective
  have hweights (q : ℤ) (hq : q ≠ 0) :
      HodgeTate.weightSpace p ι
        ((τ.quotient S.toSubmodule S.apply_mem_toSubmodule).restrictScalars ℚ_[p]) q = ⊥ :=
    (HodgeTate.weightSpace_eq_bot_iff (ι := ι)
      (qEq.restrictScalars ℚ_[p]) q).mp (W.weights_zero q hq)
  exact ⟨⟨S, hdim, hcomp, hweights⟩⟩

private theorem weightZeroQuotient_iff_of_equiv
    (p : ℕ) [Fact p.Prime]
    {K E G V U : Type*} [Field K] [Field E]
    [Algebra ℚ_[p] K] [Algebra ℚ_[p] E]
    [Algebra K ℂ_[p]] [IsScalarTower ℚ_[p] K ℂ_[p]]
    [Group G] [AddCommGroup V] [Module E V] [Module ℚ_[p] V]
    [IsScalarTower ℚ_[p] E V]
    [AddCommGroup U] [Module E U] [Module ℚ_[p] U]
    [IsScalarTower ℚ_[p] E U]
    (ι : G →* (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p))
    (hK : ∀ (g : G) (a : K), PadicComplex.galoisEquiv p (ι g)
      (algebraMap K ℂ_[p] a) = algebraMap K ℂ_[p] a)
    {ρ : Representation E G V} {τ : Representation E G U}
    (e : ρ.Equiv τ) :
    Nonempty (HodgeTate.WeightZeroQuotient p ι hK ρ) ↔
      Nonempty (HodgeTate.WeightZeroQuotient p ι hK τ) :=
  ⟨fun ⟨W⟩ => weightZeroQuotient_of_equiv p ι hK e W,
    fun ⟨W⟩ => weightZeroQuotient_of_equiv p ι hK e.symm W⟩

private theorem finiteCharacterTensor_weightZeroQuotient_iff
    (p : ℕ) [Fact p.Prime]
    {K E V : Type*} [Field K] [Algebra ℚ_[p] K]
    [Algebra K (PadicAlgCl p)] [IsScalarTower ℚ_[p] K (PadicAlgCl p)]
    [Algebra K ℂ_[p]]
    [hKC : @IsScalarTower K (PadicAlgCl p) ℂ_[p]
      Algebra.toSMul Algebra.toSMul Algebra.toSMul]
    [hQKC : @IsScalarTower ℚ_[p] K ℂ_[p]
      Algebra.toSMul Algebra.toSMul Algebra.toSMul]
    [Field E] [Algebra ℚ_[p] E] [FiniteDimensional ℚ_[p] E]
    [TopologicalSpace Eˣ] [T1Space Eˣ]
    [AddCommGroup V] [Module E V] [Module ℚ_[p] V]
    [IsScalarTower ℚ_[p] E V]
    (ρ : Representation E Gal(PadicAlgCl p/K) V)
    (χ : Gal(PadicAlgCl p/K) →* Eˣ)
    (hχ : Continuous χ) (horder : IsOfFinOrder χ) :
    Nonempty (HodgeTate.WeightZeroQuotient p
      (AlgEquiv.restrictScalarsHom ℚ_[p])
      (PadicComplex.localGalois_fixes_base p (K := K))
      ((Representation.ofCharacter χ).tprod ρ)) ↔
    Nonempty (HodgeTate.WeightZeroQuotient p
      (AlgEquiv.restrictScalarsHom ℚ_[p])
      (PadicComplex.localGalois_fixes_base p (K := K)) ρ) := by
  exact (HodgeTate.nonempty_weightZeroQuotient_iff p
    (AlgEquiv.restrictScalarsHom ℚ_[p])
    (PadicComplex.localGalois_fixes_base p (K := K))
    ((Representation.ofCharacter χ).tprod ρ)).trans
      ((HodgeTate.finiteCharacterTensor_exists_weight_zero_quotient_iff
        p ρ χ hχ horder).trans
        (HodgeTate.nonempty_weightZeroQuotient_iff p
          (AlgEquiv.restrictScalarsHom ℚ_[p])
          (PadicComplex.localGalois_fixes_base p (K := K)) ρ).symm)

/-- The actual selected effective Euler fibre underlying its arithmetic
action at one parameter and coefficient realization. -/
abbrev chosenEffectiveEulerFiber
    (N m p : ℕ) [NeZero N] [Fact p.Prime]
    (h3 : 3 ≤ N) (hmPos : 0 < m) (hmN : m < N) (hcop : m.Coprime N)
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra ℚ_[p] L] [ContinuousSMul ℚ_[p] L]
    [FiniteDimensional ℚ_[p] L] [Algebra ℚ L]
    (ι : cyclotomicField N →+* L)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N)) : Type :=
  let 𝒞 := chosenCoprimeEulerFamily N m h3 hmPos hmN hcop
  let R := chosenCoprimeRawEulerRealization N m h3 hmPos hmN hcop
  ((R.placeDescent N m 𝒞 p L ι).localSystem.toFunctor.obj
    (Scheme.etaleFiberPoint _ _ (ProjectiveLine.puncturedPoint _ ξ)))

/-- Rational `p`-adic scalars on the actual selected Euler fibre come from
its fixed coefficient field `L`. -/
@[instance_reducible] def chosenEffectiveEulerFiberPadicModule
    (N m p : ℕ) [NeZero N] [Fact p.Prime]
    (h3 : 3 ≤ N) (hmPos : 0 < m) (hmN : m < N) (hcop : m.Coprime N)
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra ℚ_[p] L] [ContinuousSMul ℚ_[p] L]
    [FiniteDimensional ℚ_[p] L] [Algebra ℚ L]
    (ι : cyclotomicField N →+* L)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N)) :
    Module ℚ_[p]
      (chosenEffectiveEulerFiber N m p h3 hmPos hmN hcop L ι ξ) :=
  Module.compHom _ (algebraMap ℚ_[p] L)

/-- The two scalar actions on the actual fibre form the expected tower. -/
theorem chosenEffectiveEulerFiberPadicScalarTower
    (N m p : ℕ) [NeZero N] [Fact p.Prime]
    (h3 : 3 ≤ N) (hmPos : 0 < m) (hmN : m < N) (hcop : m.Coprime N)
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra ℚ_[p] L] [ContinuousSMul ℚ_[p] L]
    [FiniteDimensional ℚ_[p] L] [Algebra ℚ L]
    (ι : cyclotomicField N →+* L)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N)) :
    letI := chosenEffectiveEulerFiberPadicModule
      N m p h3 hmPos hmN hcop L ι ξ
    IsScalarTower ℚ_[p] L
      (chosenEffectiveEulerFiber N m p h3 hmPos hmN hcop L ι ξ) := by
  let : Module ℚ_[p]
      (chosenEffectiveEulerFiber N m p h3 hmPos hmN hcop L ι ξ) :=
    chosenEffectiveEulerFiberPadicModule N m p h3 hmPos hmN hcop L ι ξ
  refine ⟨?_⟩
  intro r a v
  rw [Algebra.smul_def]
  change (algebraMap ℚ_[p] L r * a) • v =
    algebraMap ℚ_[p] L r • (a • v)
  exact mul_smul _ _ _

attribute [local instance] chosenEffectiveEulerFiberPadicModule
  chosenEffectiveEulerFiberPadicScalarTower

variable (N m p : ℕ) [NeZero N] [Fact p.Prime]
  (h3 : 3 ≤ N) (hmPos : 0 < m) (hmN : m < N) (hcop : m.Coprime N)
  (w : HeightOneSpectrum (𝓞 (cyclotomicField N)))
  [w.asIdeal.LiesOver (Ideal.span {(p : ℤ)})]
  (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
  [Algebra (w.adicCompletion (cyclotomicField N)) L]
  [ContinuousSMul (w.adicCompletion (cyclotomicField N)) L]
  [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
  [IsScalarTower ℚ_[p] (w.adicCompletion (cyclotomicField N)) L]
  [Algebra ℚ L] [IsScalarTower ℚ (w.adicCompletion (cyclotomicField N)) L]

/-- At every actual base prime above the fixed coefficient characteristic,
the selected effective Euler action has a genuine rank-one weight-zero
quotient at `ξ` exactly when it has one at `1 - ξ`. The witness type retains
the stable kernel, bijective comparison, and every labelled weight-zero
condition. The global quadratic character is selected before all `ξ`; its
local restriction is the one through `localGaloisRestriction`.
This is the near-ordinary consequence of [TripathiGoswamiRevised,
Lemma `lem:involution`], conditional on the named cusp and Hodge–Tate
literature inputs in its dependency cone. -/
theorem chosenEffectiveEuler_weightZeroQuotient_complement_iff
    (q : HeightOneSpectrum (𝓞 (realCyclotomicField N)))
    [q.asIdeal.LiesOver (Ideal.span {(p : ℤ)})] :
    let K := realCyclotomicField N
    let ι := coprimeEulerCoefficientMap N w L
    let s := localGaloisRestriction p K q
    ∀ ξ : ProjectiveLine.Parameter K,
      Nonempty (HodgeTate.WeightZeroQuotient p
        (AlgEquiv.restrictScalarsHom ℚ_[p])
        (PadicComplex.localGalois_fixes_base p
          (K := q.adicCompletion K))
        ((chosenEffectiveEulerAction N m p h3 hmPos hmN hcop L ι ξ).comp s)) ↔
      Nonempty (HodgeTate.WeightZeroQuotient p
        (AlgEquiv.restrictScalarsHom ℚ_[p])
        (PadicComplex.localGalois_fixes_base p
          (K := q.adicCompletion K))
        ((chosenEffectiveEulerAction N m p h3 hmPos hmN hcop L ι
          (ProjectiveLine.complementParameter K ξ)).comp s)) := by
  dsimp only
  let K := realCyclotomicField N
  let ι := coprimeEulerCoefficientMap N w L
  let s := localGaloisRestriction p K q
  obtain ⟨ν, hνc, hνsq, _, hall⟩ :=
    exists_quadratic_character_chosenEffectiveEuler_complement
      N m p h3 hmPos hmN hcop w L
  let χ := ν.comp s
  have hχ : Continuous χ :=
    hνc.comp (continuous_localGaloisRestriction p K q)
  have horder : IsOfFinOrder χ := by
    apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨2, by decide, ?_⟩
    apply MonoidHom.ext
    intro g
    have h := congrArg (fun f => f (s g)) hνsq
    simpa [χ, pow_apply] using h
  intro ξ
  obtain ⟨e⟩ := hall ξ
  have eLocal : (((Representation.ofCharacter χ).tprod
      ((chosenEffectiveEulerAction N m p h3 hmPos hmN hcop L ι ξ).comp s)).Equiv
      ((chosenEffectiveEulerAction N m p h3 hmPos hmN hcop L ι
        (ProjectiveLine.complementParameter K ξ)).comp s)) := by
    simpa only [characterTensor_comp] using e.compHom s
  have htwist := finiteCharacterTensor_weightZeroQuotient_iff p
    ((chosenEffectiveEulerAction N m p h3 hmPos hmN hcop L ι ξ).comp s)
      χ hχ horder
  have hequiv := weightZeroQuotient_iff_of_equiv p
    (AlgEquiv.restrictScalarsHom ℚ_[p])
    (PadicComplex.localGalois_fixes_base p
      (K := q.adicCompletion K)) eLocal
  exact htwist.symm.trans hequiv

/-- The covariant dual of the actual selected Euler fibre has a rank-one
weight-zero local quotient at `ξ` exactly when its complementary covariant
dual does. The cohomological comparison character is inverted by duality;
its quadraticity identifies the inverse with the same finite character. -/
theorem chosenEffectiveEuler_covariantWeightZeroQuotient_complement_iff
    (q : HeightOneSpectrum (𝓞 (realCyclotomicField N)))
    [q.asIdeal.LiesOver (Ideal.span {(p : ℤ)})] :
    let K := realCyclotomicField N
    let ι := coprimeEulerCoefficientMap N w L
    let s := localGaloisRestriction p K q
    ∀ ξ : ProjectiveLine.Parameter K,
      Nonempty (HodgeTate.WeightZeroQuotient p
        (AlgEquiv.restrictScalarsHom ℚ_[p])
        (PadicComplex.localGalois_fixes_base p
          (K := q.adicCompletion K))
        ((chosenEffectiveEulerAction N m p h3 hmPos hmN hcop L ι ξ).dual.comp s)) ↔
      Nonempty (HodgeTate.WeightZeroQuotient p
        (AlgEquiv.restrictScalarsHom ℚ_[p])
        (PadicComplex.localGalois_fixes_base p
          (K := q.adicCompletion K))
        ((chosenEffectiveEulerAction N m p h3 hmPos hmN hcop L ι
          (ProjectiveLine.complementParameter K ξ)).dual.comp s)) := by
  dsimp only
  let K := realCyclotomicField N
  let ι := coprimeEulerCoefficientMap N w L
  let s := localGaloisRestriction p K q
  obtain ⟨ν, hνc, hνsq, _, hall⟩ :=
    exists_quadratic_character_chosenEffectiveEuler_complement
      N m p h3 hmPos hmN hcop w L
  let χ := ν.comp s
  have hχ : Continuous χ :=
    hνc.comp (continuous_localGaloisRestriction p K q)
  have horder : IsOfFinOrder χ := by
    apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨2, by decide, ?_⟩
    apply MonoidHom.ext
    intro g
    have h := congrArg (fun f => f (s g)) hνsq
    simpa [χ, pow_apply] using h
  intro ξ
  let Aξ := chosenEffectiveEulerAction N m p h3 hmPos hmN hcop L ι ξ
  let Aη := chosenEffectiveEulerAction N m p h3 hmPos hmN hcop L ι
    (ProjectiveLine.complementParameter K ξ)
  obtain ⟨e⟩ := hall ξ
  have eDualGlobal : ((Representation.ofCharacter ν).tprod Aξ.dual).Equiv
      Aη.dual :=
    quadraticDualTensorEquiv Aξ Aη ν hνsq e
  have eLocal : ((Representation.ofCharacter χ).tprod
      (Aξ.dual.comp s)).Equiv (Aη.dual.comp s) := by
    simpa only [characterTensor_comp] using eDualGlobal.compHom s
  have htwist := finiteCharacterTensor_weightZeroQuotient_iff p
    (Aξ.dual.comp s) χ hχ horder
  have hequiv := weightZeroQuotient_iff_of_equiv p
    (AlgEquiv.restrictScalarsHom ℚ_[p])
    (PadicComplex.localGalois_fixes_base p
      (K := q.adicCompletion K)) eLocal
  exact htwist.symm.trans hequiv

end HilbertModularity.Hypergeometric
