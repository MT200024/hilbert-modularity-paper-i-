/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.PadicGalois
public import HilbertModularity.NumberTheory.CyclotomicCharacter
public import HilbertModularity.RepresentationTheory.ScalarRestriction
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import HilbertModularity.RepresentationTheory.Quotient

/-! # Hodge–Tate period spaces

We construct the diagonal action on `ℂ_[p] ⊗[ℚ_[p]] V` and its cyclotomic
eigenspaces. We follow the spaces `W[q]` of [src_brinon_conrad, Remark 2.3.2]:
weight `q` corresponds to the eigencharacter `χ⁻ᵠ`. No Hodge–Tate comparison
isomorphism or finiteness of these spaces is assumed here.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace PadicComplex

variable (p : ℕ) [Fact p.Prime]

/-- The actual Galois action on `ℂ_[p]`, viewed as a `ℚ_[p]`-linear representation. -/
def galoisRepresentation :
    Representation ℚ_[p] (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) ℂ_[p] where
  toFun g := (galoisEquiv p g).toLinearMap
  map_one' := by ext x; simp
  map_mul' g h := by ext x; exact congrArg (fun e => e x) (galoisEquiv_mul p g h)

end PadicComplex

namespace HodgeTate

variable (p : ℕ) [Fact p.Prime]
variable {G V W : Type*} [Group G] [AddCommGroup V] [Module ℚ_[p] V]
  [AddCommGroup W] [Module ℚ_[p] W]
variable (ι : G →* (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p))

/-- The diagonal period action, with Galois acting on both tensor factors. -/
def periodRepresentation (ρ : Representation ℚ_[p] G V) :
    Representation ℚ_[p] G (ℂ_[p] ⊗[ℚ_[p]] V) :=
  Representation.tprod ((PadicComplex.galoisRepresentation p).comp ι) ρ

/-- The period action on a pure tensor is the actual semilinear diagonal action. -/
@[simp]
theorem periodRepresentation_tmul (ρ : Representation ℚ_[p] G V)
    (g : G) (c : ℂ_[p]) (v : V) :
    periodRepresentation p ι ρ g (c ⊗ₜ[ℚ_[p]] v) =
      PadicComplex.galoisEquiv p (ι g) c ⊗ₜ[ℚ_[p]] ρ g v := rfl

/-- The diagonal period action is semilinear for the actual Galois action on `ℂ_[p]`. -/
theorem periodRepresentation_smul (ρ : Representation ℚ_[p] G V)
    (g : G) (c : ℂ_[p]) (x : ℂ_[p] ⊗[ℚ_[p]] V) :
    periodRepresentation p ι ρ g (c • x) =
      PadicComplex.galoisEquiv p (ι g) c • periodRepresentation p ι ρ g x := by
  induction x using TensorProduct.inductionOn with
  | tmul a v =>
      change PadicComplex.galoisEquiv p (ι g) (c * a) ⊗ₜ[ℚ_[p]] ρ g v =
        (PadicComplex.galoisEquiv p (ι g) c * PadicComplex.galoisEquiv p (ι g) a) ⊗ₜ[ℚ_[p]] ρ g v
      rw [map_mul]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

/-- The cyclotomic eigenspace of weight `q` inside the actual period tensor. -/
def weightSpace (ρ : Representation ℚ_[p] G V) (q : ℤ) :
    Submodule ℚ_[p] (ℂ_[p] ⊗[ℚ_[p]] V) :=
  ⨅ g : G, Module.End.eigenspace (periodRepresentation p ι ρ g)
    (((Field.cyclotomicCharacterWithCoefficients ℚ_[p] p ℚ_[p] (ι g)) ^ (-q) : ℚ_[p]ˣ) : ℚ_[p])

/-- Membership in the period eigenspace is the cyclotomic eigencharacter equation. -/
theorem mem_weightSpace (ρ : Representation ℚ_[p] G V) (q : ℤ)
    (x : ℂ_[p] ⊗[ℚ_[p]] V) :
    x ∈ weightSpace p ι ρ q ↔ ∀ g : G, periodRepresentation p ι ρ g x =
      (((Field.cyclotomicCharacterWithCoefficients ℚ_[p] p ℚ_[p] (ι g)) ^ (-q) : ℚ_[p]ˣ) : ℚ_[p]) • x := by
  simp [weightSpace]

variable {p ι} {ρ : Representation ℚ_[p] G V} {τ : Representation ℚ_[p] G W}

/-- An intertwining linear equivalence transports the actual period tensors. -/
def periodEquiv (e : ρ.Equiv τ) :
    (periodRepresentation p ι ρ).Equiv (periodRepresentation p ι τ) :=
  Representation.Equiv.mk
    (TensorProduct.congr (LinearEquiv.refl ℚ_[p] ℂ_[p]) e.toLinearEquiv) (by
      intro g
      ext c v
      change PadicComplex.galoisEquiv p (ι g) c ⊗ₜ[ℚ_[p]] e (ρ g v) =
        PadicComplex.galoisEquiv p (ι g) c ⊗ₜ[ℚ_[p]] τ g (e v)
      exact congrArg (fun w => PadicComplex.galoisEquiv p (ι g) c ⊗ₜ[ℚ_[p]] w)
        (congrArg (fun f : V →ₗ[ℚ_[p]] W => f v) (e.isIntertwining' g)))

/-- The period equivalence preserves each cyclotomic eigencharacter equation. -/
theorem periodEquiv_mem_weightSpace_iff (e : ρ.Equiv τ) (q : ℤ)
    (x : ℂ_[p] ⊗[ℚ_[p]] V) :
    periodEquiv (ι := ι) e x ∈ weightSpace p ι τ q ↔ x ∈ weightSpace p ι ρ q := by
  simp only [mem_weightSpace]
  apply forall_congr'
  intro g
  have he : periodEquiv (ι := ι) e (periodRepresentation p ι ρ g x) =
      periodRepresentation p ι τ g (periodEquiv (ι := ι) e x) :=
    congrArg (fun f : (ℂ_[p] ⊗[ℚ_[p]] V) →ₗ[ℚ_[p]] (ℂ_[p] ⊗[ℚ_[p]] W) => f x)
      ((periodEquiv (ι := ι) e).isIntertwining' g)
  rw [← he, ← map_smul (periodEquiv (ι := ι) e)]
  exact (periodEquiv (ι := ι) e).toLinearEquiv.injective.eq_iff

/-- Isomorphic representations have isomorphic actual period eigenspaces. -/
def weightSpaceEquiv (e : ρ.Equiv τ) (q : ℤ) :
    weightSpace p ι ρ q ≃ₗ[ℚ_[p]] weightSpace p ι τ q :=
  (periodEquiv (ι := ι) e).toLinearEquiv.ofSubmodules _ _ (by
    ext y
    obtain ⟨x, rfl⟩ := (periodEquiv (ι := ι) e).toLinearEquiv.surjective y
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨z, hz, he⟩
      have hzx : z = x := (periodEquiv (ι := ι) e).toLinearEquiv.injective he
      exact (periodEquiv_mem_weightSpace_iff e q x).mpr (hzx ▸ hz)
    · intro hx
      exact ⟨x, (periodEquiv_mem_weightSpace_iff e q x).mp hx, rfl⟩)

/-- The dimensions of each concrete period eigenspace are preserved. -/
theorem finrank_weightSpace_eq (e : ρ.Equiv τ) (q : ℤ) :
    Module.finrank ℚ_[p] (weightSpace p ι ρ q) =
      Module.finrank ℚ_[p] (weightSpace p ι τ q) :=
  (weightSpaceEquiv (ι := ι) e q).finrank_eq

/-- Vanishing of each concrete period eigenspace is invariant under an intertwining equivalence. -/
theorem weightSpace_eq_bot_iff (e : ρ.Equiv τ) (q : ℤ) :
    weightSpace p ι ρ q = ⊥ ↔ weightSpace p ι τ q = ⊥ := by
  constructor
  · intro h
    apply eq_bot_iff.mpr
    intro y hy
    change y = 0
    obtain ⟨x, rfl⟩ := (periodEquiv (ι := ι) e).toLinearEquiv.surjective y
    have hx := (periodEquiv_mem_weightSpace_iff e q x).mp hy
    have hx0 : x = 0 := by simpa [h] using hx
    simp [hx0]
  · intro h
    apply eq_bot_iff.mpr
    intro x hx
    change x = 0
    have hy := (periodEquiv_mem_weightSpace_iff e q x).mpr hx
    have hy0 : periodEquiv (ι := ι) e x = 0 := by simpa [h] using hy
    exact (periodEquiv (ι := ι) e).toLinearEquiv.map_eq_zero_iff.mp hy0

section Coefficients

variable {E : Type*} [Field E] [Algebra ℚ_[p] E]
  (σ : E ≃ₐ[ℚ_[p]] E) (A : Rep E G)
  [Module ℚ_[p] A] [IsScalarTower ℚ_[p] E A]
  [Module ℚ_[p] (Rep.scalarConjugate σ.toRingEquiv A)]
  [IsScalarTower ℚ_[p] E (Rep.scalarConjugate σ.toRingEquiv A)]

/-- Conjugating the coefficient field preserves the actual unlabelled period eigenspaces. -/
def scalarConjugateWeightSpaceEquiv (q : ℤ) :
    weightSpace p ι (Representation.restrictScalars ℚ_[p] A.ρ) q ≃ₗ[ℚ_[p]]
      weightSpace p ι (Representation.restrictScalars ℚ_[p]
        (Rep.scalarConjugate σ.toRingEquiv A).ρ) q :=
  weightSpaceEquiv (ι := ι) (Rep.scalarConjugateRestrictScalarsEquiv ℚ_[p] σ A) q

/-- Coefficient conjugation preserves vanishing of every nonzero-weight period eigenspace. -/
theorem scalarConjugate_nonzero_weightSpace_eq_bot_iff :
    (∀ q : ℤ, q ≠ 0 →
      weightSpace p ι (Representation.restrictScalars ℚ_[p] A.ρ) q = ⊥) ↔
    ∀ q : ℤ, q ≠ 0 → weightSpace p ι (Representation.restrictScalars ℚ_[p]
      (Rep.scalarConjugate σ.toRingEquiv A).ρ) q = ⊥ := by
  apply forall_congr'
  intro q
  exact imp_congr_right fun _ => weightSpace_eq_bot_iff
    (Rep.scalarConjugateRestrictScalarsEquiv ℚ_[p] σ A) q

end Coefficients

/-- The period equivalence is linear over the completed coefficient field on the first factor. -/
def periodLinearEquiv (e : ρ.Equiv τ) :
    (ℂ_[p] ⊗[ℚ_[p]] V) ≃ₗ[ℂ_[p]] (ℂ_[p] ⊗[ℚ_[p]] W) :=
  TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl ℂ_[p] ℂ_[p]) e.toLinearEquiv

/-- The completed-field linear equivalence is the underlying period intertwiner. -/
theorem periodLinearEquiv_apply (e : ρ.Equiv τ) (x : ℂ_[p] ⊗[ℚ_[p]] V) :
    periodLinearEquiv e x = periodEquiv (ι := ι) e x := rfl

/-- The completed-field span of fixed periods, used in the weight-zero comparison. -/
def zeroWeightSpan (ρ : Representation ℚ_[p] G V) :
    Submodule ℂ_[p] (ℂ_[p] ⊗[ℚ_[p]] V) :=
  Submodule.span ℂ_[p] (weightSpace p ι ρ 0 : Set (ℂ_[p] ⊗[ℚ_[p]] V))

/-- An intertwiner transports the full span of the actual fixed periods. -/
theorem map_zeroWeightSpan (e : ρ.Equiv τ) :
    (zeroWeightSpan (ι := ι) ρ).map (periodLinearEquiv e).toLinearMap =
      zeroWeightSpan (ι := ι) τ := by
  rw [zeroWeightSpan, Submodule.map_span, zeroWeightSpan]
  congr 1
  ext y
  obtain ⟨x, rfl⟩ := (periodLinearEquiv e).surjective y
  constructor
  · rintro ⟨z, hz, he⟩
    have hzx : z = x := (periodLinearEquiv e).injective he
    rw [periodLinearEquiv_apply]
    exact (periodEquiv_mem_weightSpace_iff e 0 x).mpr (hzx ▸ hz)
  · intro hx
    refine ⟨x, ?_, rfl⟩
    rw [periodLinearEquiv_apply] at hx
    exact (periodEquiv_mem_weightSpace_iff e 0 x).mp hx

/-- Fixed periods span the whole period tensor for one representation exactly when they do
for an isomorphic representation. -/
theorem zeroWeightSpan_eq_top_iff (e : ρ.Equiv τ) :
    zeroWeightSpan (ι := ι) ρ = ⊤ ↔ zeroWeightSpan (ι := ι) τ = ⊤ := by
  rw [← map_zeroWeightSpan e]
  exact (Submodule.map_eq_top_iff (e := periodLinearEquiv e)).symm

/-- Conjugating coefficients preserves the assertion that fixed periods span the full tensor. -/
theorem scalarConjugate_zeroWeightSpan_eq_top_iff
    {E : Type*} [Field E] [Algebra ℚ_[p] E] (σ : E ≃ₐ[ℚ_[p]] E) (A : Rep E G)
    [Module ℚ_[p] A] [IsScalarTower ℚ_[p] E A]
    [Module ℚ_[p] (Rep.scalarConjugate σ.toRingEquiv A)]
    [IsScalarTower ℚ_[p] E (Rep.scalarConjugate σ.toRingEquiv A)] :
    zeroWeightSpan (ι := ι) (Representation.restrictScalars ℚ_[p] A.ρ) = ⊤ ↔
      zeroWeightSpan (ι := ι) (Representation.restrictScalars ℚ_[p]
        (Rep.scalarConjugate σ.toRingEquiv A).ρ) = ⊤ :=
  zeroWeightSpan_eq_top_iff (Rep.scalarConjugateRestrictScalarsEquiv ℚ_[p] σ A)

/-- Coefficient conjugation preserves the existence of a stable rank-one quotient whose
period tensor is spanned by its actual Galois-fixed periods. -/
theorem scalarConjugate_exists_quotient_spanned_by_fixed_periods_iff
    {E : Type*} [Field E] [Algebra ℚ_[p] E] (σ : E ≃ₐ[ℚ_[p]] E) (A : Rep E G)
    [Module ℚ_[p] A] [IsScalarTower ℚ_[p] E A]
    [Module ℚ_[p] (Rep.scalarConjugate σ.toRingEquiv A)]
    [IsScalarTower ℚ_[p] E (Rep.scalarConjugate σ.toRingEquiv A)] :
    (∃ S : Subrepresentation A.ρ,
      Module.finrank E (A ⧸ S.toSubmodule) = 1 ∧
      zeroWeightSpan (ι := ι) (Representation.restrictScalars ℚ_[p]
        (A.ρ.quotient S.toSubmodule S.apply_mem_toSubmodule)) = ⊤) ↔
    ∃ T : Subrepresentation (Rep.scalarConjugate σ.toRingEquiv A).ρ,
      Module.finrank E (Rep.scalarConjugate σ.toRingEquiv A ⧸ T.toSubmodule) = 1 ∧
      zeroWeightSpan (ι := ι) (Representation.restrictScalars ℚ_[p]
        ((Rep.scalarConjugate σ.toRingEquiv A).ρ.quotient
          T.toSubmodule T.apply_mem_toSubmodule)) = ⊤ := by
  constructor
  · rintro ⟨S, hdim, hspan⟩
    refine ⟨Rep.scalarConjugateSubrepresentationEquiv σ.toRingEquiv A S, ?_, ?_⟩
    · exact (Rep.finrank_scalarConjugate_quotient σ.toRingEquiv A S).trans hdim
    · exact (zeroWeightSpan_eq_top_iff
        (Rep.scalarConjugateQuotientRestrictScalarsEquiv ℚ_[p] σ A S)).mp hspan
  · rintro ⟨T, hdim, hspan⟩
    obtain ⟨S, rfl⟩ := (Rep.scalarConjugateSubrepresentationEquiv σ.toRingEquiv A).surjective T
    refine ⟨S, ?_, ?_⟩
    · exact (Rep.finrank_scalarConjugate_quotient σ.toRingEquiv A S).symm.trans hdim
    · exact (zeroWeightSpan_eq_top_iff
        (Rep.scalarConjugateQuotientRestrictScalarsEquiv ℚ_[p] σ A S)).mpr hspan

/-- The period tensor of a product is the product of the period tensors, linearly over `Cp`. -/
def periodProductLinearEquiv :
    (ℂ_[p] ⊗[ℚ_[p]] (V × W)) ≃ₗ[ℂ_[p]]
      (ℂ_[p] ⊗[ℚ_[p]] V) × (ℂ_[p] ⊗[ℚ_[p]] W) :=
  TensorProduct.prodRight ℚ_[p] ℂ_[p] ℂ_[p] V W

/-- The tensor-product distribution isomorphism commutes with the diagonal Galois action. -/
theorem periodProductLinearEquiv_apply_action (ρ : Representation ℚ_[p] G V)
    (τ : Representation ℚ_[p] G W) (g : G) (x : ℂ_[p] ⊗[ℚ_[p]] (V × W)) :
    periodProductLinearEquiv (periodRepresentation p ι (ρ.prod τ) g x) =
      ((periodRepresentation p ι ρ).prod (periodRepresentation p ι τ)) g
        (periodProductLinearEquiv x) := by
  induction x using TensorProduct.inductionOn with
  | tmul c v => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- A period of a product has weight `q` precisely when both its components do. -/
theorem periodProductLinearEquiv_mem_weightSpace (ρ : Representation ℚ_[p] G V)
    (τ : Representation ℚ_[p] G W) (q : ℤ) (x : ℂ_[p] ⊗[ℚ_[p]] (V × W)) :
    x ∈ weightSpace p ι (ρ.prod τ) q ↔
      (periodProductLinearEquiv x).1 ∈ weightSpace p ι ρ q ∧
      (periodProductLinearEquiv x).2 ∈ weightSpace p ι τ q := by
  simp only [mem_weightSpace]
  rw [← forall_and]
  apply forall_congr'
  intro g
  rw [← (periodProductLinearEquiv (p := p) (V := V) (W := W)).injective.eq_iff]
  rw [periodProductLinearEquiv_apply_action]
  have hs (a : ℚ_[p]) : periodProductLinearEquiv (a • x) =
      a • periodProductLinearEquiv x :=
    (periodProductLinearEquiv (p := p) (V := V) (W := W)).toLinearMap.map_smul_of_tower a x
  rw [hs]
  exact Prod.ext_iff

/-- Fixed periods of a product span exactly the product of the two fixed-period spans. -/
theorem map_zeroWeightSpan_prod (ρ : Representation ℚ_[p] G V)
    (τ : Representation ℚ_[p] G W) :
    (zeroWeightSpan (ι := ι) (ρ.prod τ)).map periodProductLinearEquiv.toLinearMap =
      (zeroWeightSpan (ι := ι) ρ).prod (zeroWeightSpan (ι := ι) τ) := by
  rw [zeroWeightSpan, Submodule.map_span, zeroWeightSpan, zeroWeightSpan,
    ← Submodule.span_prod_eq ℂ_[p] (weightSpace p ι ρ 0).zero_mem
      (weightSpace p ι τ 0).zero_mem]
  congr 1
  ext y
  obtain ⟨x, rfl⟩ := (periodProductLinearEquiv (p := p) (V := V) (W := W)).surjective y
  constructor
  · rintro ⟨z, hz, he⟩
    have hzx : z = x := (periodProductLinearEquiv (p := p) (V := V) (W := W)).injective he
    exact (periodProductLinearEquiv_mem_weightSpace ρ τ 0 x).mp (hzx ▸ hz)
  · intro hx
    exact ⟨x, (periodProductLinearEquiv_mem_weightSpace ρ τ 0 x).mpr hx, rfl⟩

/-- A product is spanned by fixed periods when each factor is. -/
theorem zeroWeightSpan_prod_eq_top (ρ : Representation ℚ_[p] G V)
    (τ : Representation ℚ_[p] G W)
    (hρ : zeroWeightSpan (ι := ι) ρ = ⊤) (hτ : zeroWeightSpan (ι := ι) τ = ⊤) :
    zeroWeightSpan (ι := ι) (ρ.prod τ) = ⊤ := by
  apply (Submodule.map_eq_top_iff (e := periodProductLinearEquiv)).mp
  rw [map_zeroWeightSpan_prod, hρ, hτ, Submodule.prod_top]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- A two-dimensional representation not spanned by fixed periods has at most one
rank-one quotient whose period tensor is spanned by fixed periods. -/
theorem eq_of_quotients_spanned_by_fixed_periods
    {E : Type*} [Field E] [Algebra ℚ_[p] E]
    [Module E V] [IsScalarTower ℚ_[p] E V] [FiniteDimensional E V]
    (ρ : Representation E G V) (hV : Module.finrank E V = 2)
    (hρ : zeroWeightSpan (ι := ι) (ρ.restrictScalars ℚ_[p]) ≠ ⊤)
    (P Q : Subrepresentation ρ)
    (hP : Module.finrank E (V ⧸ P.toSubmodule) = 1)
    (hQ : Module.finrank E (V ⧸ Q.toSubmodule) = 1)
    (hfixedP : zeroWeightSpan (ι := ι) ((ρ.quotient P.toSubmodule
      P.apply_mem_toSubmodule).restrictScalars ℚ_[p]) = ⊤)
    (hfixedQ : zeroWeightSpan (ι := ι) ((ρ.quotient Q.toSubmodule
      Q.apply_mem_toSubmodule).restrictScalars ℚ_[p]) = ⊤) : P = Q := by
  by_contra hne
  have hprod : zeroWeightSpan (ι := ι)
      (((ρ.quotient P.toSubmodule P.apply_mem_toSubmodule).restrictScalars ℚ_[p]).prod
        ((ρ.quotient Q.toSubmodule Q.apply_mem_toSubmodule).restrictScalars ℚ_[p])) = ⊤ :=
    zeroWeightSpan_prod_eq_top _ _ hfixedP hfixedQ
  let e : (ρ.restrictScalars ℚ_[p]).Equiv
      (((ρ.quotient P.toSubmodule P.apply_mem_toSubmodule).restrictScalars ℚ_[p]).prod
        ((ρ.quotient Q.toSubmodule Q.apply_mem_toSubmodule).restrictScalars ℚ_[p])) :=
    (ρ.quotientPairEquiv P Q hV hP hQ hne).restrictScalars ℚ_[p]
  exact hρ ((zeroWeightSpan_eq_top_iff (ι := ι) e).mpr hprod)

/-- An intertwiner induces a `Cp`-linear map on period tensors. -/
def periodLinearMap (f : ρ.IntertwiningMap τ) :
    (ℂ_[p] ⊗[ℚ_[p]] V) →ₗ[ℂ_[p]] (ℂ_[p] ⊗[ℚ_[p]] W) :=
  TensorProduct.AlgebraTensorModule.lTensor ℂ_[p] ℂ_[p] f.toLinearMap

/-- The induced period map carries each actual cyclotomic eigenspace into the corresponding one. -/
theorem periodLinearMap_mem_weightSpace (f : ρ.IntertwiningMap τ) (q : ℤ)
    (x : ℂ_[p] ⊗[ℚ_[p]] V) (hx : x ∈ weightSpace p ι ρ q) :
    periodLinearMap f x ∈ weightSpace p ι τ q := by
  rw [mem_weightSpace] at hx ⊢
  intro g
  let F := f.lTensor ((PadicComplex.galoisRepresentation p).comp ι)
  have he := congrArg (fun l : (ℂ_[p] ⊗[ℚ_[p]] V) →ₗ[ℚ_[p]]
      (ℂ_[p] ⊗[ℚ_[p]] W) => l x) (F.isIntertwining' g)
  change periodLinearMap f (periodRepresentation p ι ρ g x) =
    periodRepresentation p ι τ g (periodLinearMap f x) at he
  rw [← he, hx g]
  exact (periodLinearMap f).map_smul_of_tower _ x

/-- Every equivariant map carries the fixed-period span into the target fixed-period span. -/
theorem map_zeroWeightSpan_le (f : ρ.IntertwiningMap τ) :
    (zeroWeightSpan (ι := ι) ρ).map (periodLinearMap f) ≤ zeroWeightSpan (ι := ι) τ := by
  rw [zeroWeightSpan, Submodule.map_span]
  apply Submodule.span_le.mpr
  rintro y ⟨x, hx, rfl⟩
  exact Submodule.subset_span (periodLinearMap_mem_weightSpace f 0 x hx)

/-- A surjective equivariant image of a representation spanned by fixed periods is also
spanned by fixed periods. -/
theorem zeroWeightSpan_eq_top_of_surjective (f : ρ.IntertwiningMap τ)
    (hf : Function.Surjective f) (hρ : zeroWeightSpan (ι := ι) ρ = ⊤) :
    zeroWeightSpan (ι := ι) τ = ⊤ := by
  have hsurj : Function.Surjective (periodLinearMap f) :=
    LinearMap.lTensor_surjective ℂ_[p] hf
  apply top_unique
  have h := map_zeroWeightSpan_le (ι := ι) f
  rwa [hρ, Submodule.map_top, LinearMap.range_eq_top.mpr hsurj] at h

/-- Spanning by fixed periods descends along a coefficient-field extension. -/
theorem zeroWeightSpan_eq_top_of_baseChange
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra ℚ_[p] K] [Algebra ℚ_[p] L] [IsScalarTower ℚ_[p] K L]
    [Module K V] [IsScalarTower ℚ_[p] K V]
    (ρ : Representation K G V)
    (hρ : zeroWeightSpan (ι := ι) ((ρ.baseChange L).restrictScalars ℚ_[p]) = ⊤) :
    zeroWeightSpan (ι := ι) (ρ.restrictScalars ℚ_[p]) = ⊤ := by
  obtain ⟨f, hf⟩ := Representation.exists_surjective_baseChange_coefficientMap (L := L) ρ
  exact zeroWeightSpan_eq_top_of_surjective (ι := ι) (f.restrictScalars ℚ_[p]) hf hρ

/-- Spanning by fixed periods is preserved by extension of the coefficient field. -/
theorem zeroWeightSpan_baseChange_eq_top
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra ℚ_[p] K] [Algebra ℚ_[p] L] [IsScalarTower ℚ_[p] K L]
    [Module K V] [IsScalarTower ℚ_[p] K V]
    (ρ : Representation K G V)
    (hρ : zeroWeightSpan (ι := ι) (ρ.restrictScalars ℚ_[p]) = ⊤) :
    zeroWeightSpan (ι := ι) ((ρ.baseChange L).restrictScalars ℚ_[p]) = ⊤ := by
  apply top_unique
  intro x hx
  clear hx
  induction x using TensorProduct.inductionOn with
  | tmul c v =>
      induction v using TensorProduct.inductionOn with
      | tmul a v =>
          let f := (Representation.baseChangeTensorMap ρ a).restrictScalars ℚ_[p]
          apply map_zeroWeightSpan_le (ι := ι) f
          exact Submodule.mem_map.mpr ⟨c ⊗ₜ[ℚ_[p]] v, by rw [hρ]; trivial, rfl⟩
      | add v w hv hw =>
          rw [TensorProduct.tmul_add]
          exact Submodule.add_mem _ hv hw
  | add x y hx hy => exact Submodule.add_mem _ hx hy

/-- The actual fixed-period spanning condition is invariant under a coefficient-field extension. -/
theorem zeroWeightSpan_baseChange_eq_top_iff
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra ℚ_[p] K] [Algebra ℚ_[p] L] [IsScalarTower ℚ_[p] K L]
    [Module K V] [IsScalarTower ℚ_[p] K V] (ρ : Representation K G V) :
    zeroWeightSpan (ι := ι) ((ρ.baseChange L).restrictScalars ℚ_[p]) = ⊤ ↔
      zeroWeightSpan (ι := ι) (ρ.restrictScalars ℚ_[p]) = ⊤ :=
  ⟨zeroWeightSpan_eq_top_of_baseChange ρ, zeroWeightSpan_baseChange_eq_top ρ⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- Equivalent representations have the same existence criterion for fixed-period rank-one quotients. -/
theorem exists_quotient_spanned_by_fixed_periods_iff
    {E : Type*} [Field E] [Algebra ℚ_[p] E]
    [Module E V] [IsScalarTower ℚ_[p] E V]
    [Module E W] [IsScalarTower ℚ_[p] E W]
    {ρ : Representation E G V} {τ : Representation E G W} (e : ρ.Equiv τ) :
    (∃ S : Subrepresentation ρ, Module.finrank E (V ⧸ S.toSubmodule) = 1 ∧
      zeroWeightSpan (ι := ι) ((ρ.quotient S.toSubmodule
        S.apply_mem_toSubmodule).restrictScalars ℚ_[p]) = ⊤) ↔
    ∃ T : Subrepresentation τ, Module.finrank E (W ⧸ T.toSubmodule) = 1 ∧
      zeroWeightSpan (ι := ι) ((τ.quotient T.toSubmodule
        T.apply_mem_toSubmodule).restrictScalars ℚ_[p]) = ⊤ := by
  constructor
  · rintro ⟨S, hdim, hspan⟩
    refine ⟨e.subrepresentationOrderIso S, ?_, ?_⟩
    · exact (e.quotientCongr S).toLinearEquiv.finrank_eq.symm.trans hdim
    · exact (zeroWeightSpan_eq_top_iff (ι := ι)
        ((e.quotientCongr S).restrictScalars ℚ_[p])).mp hspan
  · rintro ⟨T, hdim, hspan⟩
    obtain ⟨S, rfl⟩ := e.subrepresentationOrderIso.surjective T
    refine ⟨S, ?_, ?_⟩
    · exact (e.quotientCongr S).toLinearEquiv.finrank_eq.trans hdim
    · exact (zeroWeightSpan_eq_top_iff (ι := ι)
        ((e.quotientCongr S).restrictScalars ℚ_[p])).mpr hspan

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- A fixed-period rank-one quotient remains such a quotient after extending coefficients. -/
theorem exists_quotient_spanned_by_fixed_periods_baseChange
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra ℚ_[p] K] [Algebra ℚ_[p] L] [IsScalarTower ℚ_[p] K L]
    [Module K V] [IsScalarTower ℚ_[p] K V] (ρ : Representation K G V)
    (hex : ∃ S : Subrepresentation ρ, Module.finrank K (V ⧸ S.toSubmodule) = 1 ∧
      zeroWeightSpan (ι := ι) ((ρ.quotient S.toSubmodule
        S.apply_mem_toSubmodule).restrictScalars ℚ_[p]) = ⊤) :
    ∃ T : Subrepresentation (ρ.baseChange L),
      Module.finrank L ((L ⊗[K] V) ⧸ T.toSubmodule) = 1 ∧
      zeroWeightSpan (ι := ι) (((ρ.baseChange L).quotient T.toSubmodule
        T.apply_mem_toSubmodule).restrictScalars ℚ_[p]) = ⊤ := by
  obtain ⟨S, hdim, hspan⟩ := hex
  refine ⟨S.baseChange L, ?_, ?_⟩
  · rw [← (Representation.quotientBaseChangeEquiv L S).toLinearEquiv.finrank_eq,
      Module.finrank_baseChange, hdim]
  · apply (zeroWeightSpan_eq_top_iff (ι := ι)
      ((Representation.quotientBaseChangeEquiv L S).restrictScalars ℚ_[p])).mp
    exact zeroWeightSpan_baseChange_eq_top _ hspan

end HodgeTate
