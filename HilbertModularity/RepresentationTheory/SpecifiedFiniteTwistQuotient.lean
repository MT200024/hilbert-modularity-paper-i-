/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.FiniteCharacterTwist
public import HilbertModularity.RepresentationTheory.WeightZeroQuotient

/-! # A specified weight-zero quotient under a finite tensor twist

The existing finite-character comparison theorem transports existence. This
module retains the particular stable kernel and computes the Galois action
on its transported quotient.
-/

public noncomputable section

open scoped TensorProduct

namespace HodgeTate

variable (p : ℕ) [Fact p.Prime]
  {K E V : Type*} [Field K] [Algebra ℚ_[p] K] [Algebra K (PadicAlgCl p)]
  [IsScalarTower ℚ_[p] K (PadicAlgCl p)] [Algebra K ℂ_[p]]
  [hKC : @IsScalarTower K (PadicAlgCl p) ℂ_[p] Algebra.toSMul Algebra.toSMul Algebra.toSMul]
  [hQKC : @IsScalarTower ℚ_[p] K ℂ_[p] Algebra.toSMul Algebra.toSMul Algebra.toSMul]
  [Field E] [Algebra ℚ_[p] E] [FiniteDimensional ℚ_[p] E]
  [TopologicalSpace Eˣ] [T1Space Eˣ]
  [AddCommGroup V] [Module E V] [Module ℚ_[p] V] [IsScalarTower ℚ_[p] E V]
  (ρ : Representation E Gal(PadicAlgCl p/K) V)
  (χ : Gal(PadicAlgCl p/K) →* Eˣ)
  (hχ : Continuous χ) (horder : IsOfFinOrder χ)

include hχ horder hKC hQKC

/-- Twisting the quotient of one specified stable kernel preserves the
canonical Hodge–Tate comparison and the vanishing of all nonzero weights.
The proof uses the actual tensor period of the finite-order character. -/
theorem characterTensor_criterion_of_weightZeroQuotient
    (W : WeightZeroQuotient p
      (AlgEquiv.restrictScalarsHom ℚ_[p])
      (PadicComplex.localGalois_fixes_base p (K := K)) ρ) :
    let T := Representation.characterTensorSubrepresentationEquiv ρ χ W.kernel
    let τQ := (((Representation.ofCharacter χ).tprod ρ).quotient
      T.toSubmodule T.apply_mem_toSubmodule).restrictScalars ℚ_[p]
    Function.Bijective (comparison p (AlgEquiv.restrictScalarsHom ℚ_[p])
      (PadicComplex.localGalois_fixes_base p (K := K)) τQ) ∧
      ∀ q : ℤ, q ≠ 0 → weightSpace p
        (AlgEquiv.restrictScalarsHom ℚ_[p]) τQ q = ⊥ := by
  let S := W.kernel
  let ρQ := ρ.quotient S.toSubmodule S.apply_mem_toSubmodule
  let T := Representation.characterTensorSubrepresentationEquiv ρ χ S
  let τQ := ((Representation.ofCharacter χ).tprod ρ).quotient
    T.toSubmodule T.apply_mem_toSubmodule
  let e : τQ.Equiv (ρQ.characterTwist χ) :=
    (Representation.characterTensorQuotientEquiv ρ χ S).trans
      (Representation.characterTwistTensorEquiv ρQ χ)
  have hbase : Function.Bijective (comparison p
      (AlgEquiv.restrictScalarsHom ℚ_[p])
      (PadicComplex.localGalois_fixes_base p (K := K))
      (ρQ.restrictScalars ℚ_[p])) ∧
      ∀ q : ℤ, q ≠ 0 → weightSpace p
        (AlgEquiv.restrictScalarsHom ℚ_[p])
        (ρQ.restrictScalars ℚ_[p]) q = ⊥ :=
    ⟨W.comparison_bijective, W.weights_zero⟩
  have htwist := (finiteCharacterTwist_comparison_and_weights_zero_iff p
    ρQ χ hχ horder).mp hbase
  let eQ := e.restrictScalars ℚ_[p]
  exact ((and_congr
    (comparison_bijective_iff p (AlgEquiv.restrictScalarsHom ℚ_[p])
      (PadicComplex.localGalois_fixes_base p (K := K)) eQ)
    (forall_congr' fun q => imp_congr_right fun _ =>
      weightSpace_eq_bot_iff (ι := AlgEquiv.restrictScalarsHom ℚ_[p]) eQ q))).mpr
      htwist

/-- If the specified source quotient is Galois fixed, its finite-character
tensor twist has exactly that character as its quotient action. -/
theorem exists_characterTensorWeightZeroQuotient_with_action
    (W : WeightZeroQuotient p
      (AlgEquiv.restrictScalarsHom ℚ_[p])
      (PadicComplex.localGalois_fixes_base p (K := K)) ρ)
    (hfixed : ∀ (g : Gal(PadicAlgCl p/K)) (v : V ⧸ W.kernel.toSubmodule),
      (ρ.quotient W.kernel.toSubmodule W.kernel.apply_mem_toSubmodule) g v = v) :
    ∃ T : WeightZeroQuotient p
        (AlgEquiv.restrictScalarsHom ℚ_[p])
        (PadicComplex.localGalois_fixes_base p (K := K))
        ((Representation.ofCharacter χ).tprod ρ),
      ∀ (g : Gal(PadicAlgCl p/K))
        (v : (E ⊗[E] V) ⧸ T.kernel.toSubmodule),
        (((Representation.ofCharacter χ).tprod ρ).quotient
          T.kernel.toSubmodule T.kernel.apply_mem_toSubmodule g v) =
            (χ g : E) • v := by
  let S := W.kernel
  let T := Representation.characterTensorSubrepresentationEquiv ρ χ S
  let ρQ := ρ.quotient S.toSubmodule S.apply_mem_toSubmodule
  let τ := (Representation.ofCharacter χ).tprod ρ
  let τQ := τ.quotient T.toSubmodule T.apply_mem_toSubmodule
  let e : τQ.Equiv (ρQ.characterTwist χ) :=
    (Representation.characterTensorQuotientEquiv ρ χ S).trans
      (Representation.characterTwistTensorEquiv ρQ χ)
  have hdim : Module.finrank E ((E ⊗[E] V) ⧸ T.toSubmodule) = 1 :=
    (Representation.finrank_characterTensor_quotient ρ χ S).trans W.finrank_eq_one
  obtain ⟨hcomp, hweights⟩ :=
    characterTensor_criterion_of_weightZeroQuotient p ρ χ hχ horder W
  let T₀ : WeightZeroQuotient p
      (AlgEquiv.restrictScalarsHom ℚ_[p])
      (PadicComplex.localGalois_fixes_base p (K := K)) τ :=
    ⟨T, hdim, hcomp, hweights⟩
  refine ⟨T₀, ?_⟩
  intro g v
  apply e.injective
  have h := LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' g) v
  change e (τQ g v) = (ρQ.characterTwist χ) g (e v) at h
  rw [Representation.characterTwist_apply, hfixed g (e v)] at h
  change e (τQ g v) = e ((χ g : E) • v)
  rw [map_smul]
  exact h

end HodgeTate

namespace HodgeTate

variable (p : ℕ) [Fact p.Prime]
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

/-- A coefficient-linear equivalence transports one specified ordinary
quotient together with its exact one-dimensional Galois character. -/
theorem exists_weightZeroQuotient_equiv_with_character
    {ρ : Representation E G V} {τ : Representation E G U}
    (e : ρ.Equiv τ)
    (χ : G →* Eˣ)
    (W : WeightZeroQuotient p ι hK ρ)
    (hact : ∀ (g : G) (v : V ⧸ W.kernel.toSubmodule),
      (ρ.quotient W.kernel.toSubmodule W.kernel.apply_mem_toSubmodule) g v =
        (χ g : E) • v) :
    ∃ T : WeightZeroQuotient p ι hK τ,
      ∀ (g : G) (v : U ⧸ T.kernel.toSubmodule),
        (τ.quotient T.kernel.toSubmodule T.kernel.apply_mem_toSubmodule) g v =
          (χ g : E) • v := by
  let S := e.subrepresentationOrderIso W.kernel
  let qEq := e.quotientCongr W.kernel
  have hdim : Module.finrank E (U ⧸ S.toSubmodule) = 1 :=
    qEq.toLinearEquiv.finrank_eq.symm.trans W.finrank_eq_one
  have hcomp : Function.Bijective (comparison p ι hK
      ((τ.quotient S.toSubmodule S.apply_mem_toSubmodule).restrictScalars ℚ_[p])) :=
    (comparison_bijective_iff p ι hK (qEq.restrictScalars ℚ_[p])).mp
      W.comparison_bijective
  have hweights (q : ℤ) (hq : q ≠ 0) :
      weightSpace p ι
        ((τ.quotient S.toSubmodule S.apply_mem_toSubmodule).restrictScalars ℚ_[p]) q = ⊥ :=
    (weightSpace_eq_bot_iff (ι := ι) (qEq.restrictScalars ℚ_[p]) q).mp
      (W.weights_zero q hq)
  let T : WeightZeroQuotient p ι hK τ := ⟨S, hdim, hcomp, hweights⟩
  refine ⟨T, ?_⟩
  intro g v
  obtain ⟨u, rfl⟩ := qEq.surjective v
  have he := LinearMap.congr_fun (qEq.toIntertwiningMap.isIntertwining' g) u
  change qEq ((ρ.quotient W.kernel.toSubmodule
      W.kernel.apply_mem_toSubmodule) g u) =
    (τ.quotient S.toSubmodule S.apply_mem_toSubmodule) g (qEq u) at he
  change (τ.quotient S.toSubmodule S.apply_mem_toSubmodule) g (qEq u) =
    (χ g : E) • qEq u
  calc
    _ = qEq ((ρ.quotient W.kernel.toSubmodule
          W.kernel.apply_mem_toSubmodule) g u) := he.symm
    _ = qEq ((χ g : E) • u) := congrArg qEq (hact g u)
    _ = (χ g : E) • qEq u := map_smul qEq.toLinearEquiv _ _

end HodgeTate
