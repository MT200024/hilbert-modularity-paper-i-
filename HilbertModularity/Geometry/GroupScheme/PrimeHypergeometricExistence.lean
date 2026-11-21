/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.HypergeometricExistence
public import HilbertModularity.Geometry.GroupScheme.FiberCoefficients
public import HilbertModularity.Geometry.GroupScheme.PrimeKernel
public import HilbertModularity.Geometry.GroupScheme.CoefficientTorsion
public import HilbertModularity.Geometry.GroupScheme.GeometricField
public import HilbertModularity.Geometry.GroupScheme.PlusCurveJacobian
public import HilbertModularity.NumberTheory.CyclotomicCharacter

/-! # One explicit prime plus family

The cited plus Jacobian is chosen once, together with its integral real multiplication
and its rational point of exact prime order. The labelled auxiliary division-point
determinant is stated separately and is not part of the existence admission.
The chosen family here is independent of the earlier abstract
`darmonFamily` witness. The joint choice keeps the arithmetic properties attached to
the same abelian scheme. See [DarmonFibres, Section 3, Example 3 and Propositions
3.2 and 3.4], [DarmonRigid, Theorem 2.6(2)] and [DarmonMestre, Section 4].
-/

public section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Matrix HilbertModularity.Cyclotomic
open scoped CategoryTheory.MonObj NumberField TensorProduct MatrixGroups ModuleCat.Algebra

namespace AlgebraicGeometry.Scheme
universe u

variable (k Ω Ω' : Type u) [Field k] [Field Ω] [Field Ω']
  [Algebra k Ω] [Algebra k Ω'] [Algebra Ω Ω'] [IsScalarTower k Ω Ω']

/-- A field extension is injective on the points of a finite scheme. Unlike the
closed-field comparison, this applies to the rational generic point. -/
theorem injective_precomp_fieldExtension_of_isFinite {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsFinite f] :
    Function.Injective (fun y : Over.mk (Spec.algebraMap k Ω) ⟶ Over.mk f =>
      (Spec.overHomEquivAlgHom k Ω Ω').symm (IsScalarTower.toAlgHom k Ω Ω') ≫ y) := by
  let : IsAffine X := isAffine_of_isAffineHom f
  let A : CommRingCat := Γ(X, ⊤)
  let a : CommRingCat.of k ⟶ A := Spec.preimage (X.isoSpec.inv ≫ f)
  let : Algebra k A := a.hom.toAlgebra
  have ha : Spec.algebraMap k A = X.isoSpec.inv ≫ f := Spec.map_preimage _
  let e : Over.mk f ≅ Over.mk (Spec.algebraMap k A) := Over.isoMk X.isoSpec (by
    change X.isoSpec.hom ≫ Spec.algebraMap k A = f
    rw [ha, ← Category.assoc, Iso.hom_inv_id, Category.id_comp])
  let eΩ := (Iso.refl (Over.mk (Spec.algebraMap k Ω))).homCongr e
  let eΩ' := (Iso.refl (Over.mk (Spec.algebraMap k Ω'))).homCongr e
  have hj : Function.Injective (fun φ : A →ₐ[k] Ω =>
      (IsScalarTower.toAlgHom k Ω Ω').comp φ) := by
    intro φ ψ h
    ext z
    apply (IsScalarTower.toAlgHom k Ω Ω').injective
    exact congrArg (fun q : A →ₐ[k] Ω' => q z) h
  have hnat (y : Over.mk (Spec.algebraMap k Ω) ⟶ Over.mk f) :
      eΩ' ((Spec.overHomEquivAlgHom k Ω Ω').symm
      (IsScalarTower.toAlgHom k Ω Ω') ≫ y) =
        (Spec.overHomEquivAlgHom k Ω Ω').symm (IsScalarTower.toAlgHom k Ω Ω') ≫ eΩ y := by
    change 𝟙 _ ≫ (_ ≫ y) ≫ e.hom = _ ≫ (𝟙 _ ≫ y ≫ e.hom)
    simp only [Category.id_comp, Category.assoc]
  intro y z he
  apply eΩ.injective
  apply (Spec.overHomEquivAlgHom k A Ω).injective
  apply hj
  have he' := congrArg (fun w => Spec.overHomEquivAlgHom k A Ω' (eΩ' w)) he
  rw [hnat y, hnat z] at he'
  simpa only [Spec.overHomEquivAlgHom_comp] using he'

/-- A finite scheme over a base has injective point map after extending the
field of a point of the base. -/
theorem injective_precomp_finiteFiber_fieldExtension {S : Scheme.{u}}
    (x : Spec (CommRingCat.of Ω) ⟶ S) (Y : Over S) [IsFinite Y.hom] :
    Function.Injective (fun y : Over.mk x ⟶ Y =>
      Over.homMk (U := Over.mk (Spec.algebraMap Ω Ω' ≫ x)) (V := Over.mk x)
        (Spec.algebraMap Ω Ω') rfl ≫ y) := by
  let A := Over.mk (Spec.algebraMap Ω Ω)
  let B := Over.mk (Spec.algebraMap Ω Ω')
  let q : B ⟶ A := (Spec.overHomEquivAlgHom Ω Ω Ω').symm
    (IsScalarTower.toAlgHom Ω Ω Ω')
  let P := (Over.pullback x).obj Y
  let : IsFinite P.hom := by
    change IsFinite (pullback.snd Y.hom x)
    infer_instance
  have h : Function.Injective (fun y : A ⟶ P => q ≫ y) :=
    injective_precomp_fieldExtension_of_isFinite Ω Ω Ω' P.hom
  let adj := Over.mapPullbackAdj x
  let eA := adj.homEquiv A Y
  let eB := adj.homEquiv B Y
  have hb : Function.Injective (fun y : (Over.map x).obj A ⟶ Y =>
      (Over.map x).map q ≫ y) := by
    intro y z he
    apply eA.injective
    apply h
    have he' := congrArg eB he
    rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_left] at he'
    exact he'
  have hq : q = Over.homMk (U := B) (V := A) (Spec.algebraMap Ω Ω')
      (by simp [A, B, Spec.algebraMap, Algebra.algebraMap_self]) := by
    apply Over.OverMorphism.ext
    exact Spec.overHomEquivAlgHom_symm_left Ω Ω Ω' _
  rw [hq] at hb
  let i : (Over.map x).obj A ≅ Over.mk x :=
    Over.isoMk (Iso.refl _) (by
      change 𝟙 _ ≫ x = Spec.algebraMap Ω Ω ≫ x
      simp [Spec.algebraMap, Algebra.algebraMap_self])
  have hh := hb.comp (i.homCongr (Iso.refl Y)).symm.injective
  change Function.Injective (fun y : Over.mk x ⟶ Y =>
    (Over.homMk (U := Over.mk (Spec.algebraMap Ω Ω' ≫ x)) (V := Over.mk x)
      (Spec.algebraMap Ω Ω') rfl) ≫ y)
  convert hh using 1
  · rfl
  funext y
  apply Over.OverMorphism.ext
  change Spec.algebraMap Ω Ω' ≫ y.left =
    Spec.algebraMap Ω Ω' ≫ (𝟙 _ ≫ y.left ≫ 𝟙 _)
  simp only [Category.id_comp, Category.comp_id]

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.GroupScheme
universe u

variable (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω]
  {S : Scheme.{u}} (x : Spec (CommRingCat.of K) ⟶ S) (A : CommGrp (Over S))

attribute [local instance] torsionObjectEtale torsionObjectIsFinite

/-- Field extension is injective on the actual finite torsion fibre even when
the rational source field is not algebraically closed. -/
theorem torsionMap_geometricPointsFieldMap_injective (p : ℕ) [Fact p.Prime] (n : ℕ)
    [IsFinite (p ^ n • 𝟙 A).hom.hom.hom.left]
    [Etale (p ^ n • 𝟙 A).hom.hom.hom.left] :
    Function.Injective (TateModule.torsionMap p (geometricPointsFieldMap K Ω x A) n) := by
  let q := Over.homMk (U := Over.mk (Spec.algebraMap K Ω ≫ x)) (V := Over.mk x)
    (Spec.algebraMap K Ω) rfl
  let e := CommGrp.torsionPointAddEquiv A (p ^ n) (Over.mk x)
  let e' := CommGrp.torsionPointAddEquiv A (p ^ n)
    (Over.mk (Spec.algebraMap K Ω ≫ x))
  have h := Scheme.injective_precomp_finiteFiber_fieldExtension K Ω x
    (CommGrp.torsionObject A (p ^ n)).X
  change Function.Injective (fun v : Over.mk x ⟶ (CommGrp.torsionObject A (p ^ n)).X =>
    q ≫ v) at h
  have hn (v : Additive (Over.mk x ⟶ (CommGrp.torsionObject A (p ^ n)).X)) :
      TateModule.torsionMap p (geometricPointsFieldMap K Ω x A) n (e v) =
        e' (Additive.ofMul (q ≫ v.toMul)) := by
    apply Subtype.ext
    change q ≫ (v.toMul ≫ Grp.kernelInclusion (p ^ n • 𝟙 A).hom) =
      (q ≫ v.toMul) ≫ Grp.kernelInclusion (p ^ n • 𝟙 A).hom
    exact (Category.assoc _ _ _).symm
  have h' : Function.Injective (fun v :
      Additive (Over.mk x ⟶ (CommGrp.torsionObject A (p ^ n)).X) =>
      Additive.ofMul (q ≫ v.toMul)) := h
  have hh := e'.injective.comp (h'.comp e.symm.injective)
  convert hh using 1
  funext v
  simpa only [Function.comp_apply, AddEquiv.apply_symm_apply] using hn (e.symm v)

end AlgebraicGeometry.GroupScheme

namespace HilbertModularity.Hypergeometric
open AlgebraicGeometry.GroupScheme

/-- The residue field map attached to a labelled auxiliary coefficient map. -/
def auxiliaryResidueMap {p ell : ℕ} [Fact p.Prime]
    {F : Type} [Field F] [CharP F ell]
    (φ : 𝓞 (realCyclotomicField p) →+* F) :
    (𝓞 (realCyclotomicField p) ⧸ Ideal.span {(ell : 𝓞 (realCyclotomicField p))}) →+* F :=
  Ideal.Quotient.lift _ φ (by
    intro r hr
    obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton.mp hr
    simp)

/-- The actual tensor-Tate realization of the base triple for one fixed family,
RM action, and set of geometric inertia generators. -/
@[expose] def PrimePlusTensorTateRealization (p : ℕ) [Fact p.Prime]
    (family : CommGrp (Over (ProjectiveLine.punctured (realCyclotomicField p))))
    (realMultiplication : 𝓞 (realCyclotomicField p) →+* End family)
    (multiplication_finite : ∀ n : ℕ, 0 < n → IsFinite (n • 𝟙 family).hom.hom.hom.left)
    (multiplication_etale : ∀ n : ℕ, 0 < n → Etale (n • 𝟙 family).hom.hom.hom.left)
    (γ : Fin 3 →
        (AlgebraicClosure (RatFunc (realCyclotomicField p)) ≃ₐ[RatFunc (realCyclotomicField p)]
          AlgebraicClosure (RatFunc (realCyclotomicField p)))) : Prop :=
    ∀ (q : ℕ) (hq : q.Prime),
        letI : Fact q.Prime := ⟨hq⟩
        letI : ∀ n : ℕ, IsFinite (q ^ n • 𝟙 family).hom.hom.hom.left :=
          fun n => multiplication_finite (q ^ n) (pow_pos hq.pos n)
        letI : ∀ n : ℕ, Etale (q ^ n • 𝟙 family).hom.hom.hom.left :=
          fun n => multiplication_etale (q ^ n) (pow_pos hq.pos n)
        let x := ProjectiveLine.puncturedRationalPoint (realCyclotomicField p)
        let V := TateModule.rational q
          (Additive (Scheme.geometricPointOver (RatFunc (realCyclotomicField p)) x ⟶ family.X))
        let Θ := GroupScheme.geometricTensorTateAction (RatFunc (realCyclotomicField p))
          family q (realCyclotomicField p) realMultiplication x
        letI : Module (ℚ_[q] ⊗[ℚ] realCyclotomicField p) V := Module.compHom V Θ.toRingHom
        ∃ b : Module.Basis (Fin 2) (ℚ_[q] ⊗[ℚ] realCyclotomicField p) V,
          ∀ (i : Fin 3) (v : V),
            (b.repr (GroupScheme.rationalTateMonodromy (RatFunc (realCyclotomicField p)) x
              family q
              (Scheme.galoisToEtaleFundamentalGroup (RatFunc (realCyclotomicField p)) x
                (γ i)) v) : Fin 2 → ℚ_[q] ⊗[ℚ] realCyclotomicField p) =
            ((Monodromy.standardTriple ((1 : ℚ_[q]) ⊗ₜ[ℚ] tau p 1) i :
              Matrix (Fin 2) (Fin 2) (ℚ_[q] ⊗[ℚ] realCyclotomicField p)) *ᵥ b.repr v)

/-- Actual tensor-Tate realization of the base triple for this family and RM action,
with one geometric inertia choice shared across every realization prime. -/
structure PrimePlusTensorTateTriple (p : ℕ) [Fact p.Prime]
    (family : CommGrp (Over (ProjectiveLine.punctured (realCyclotomicField p))))
    (realMultiplication : 𝓞 (realCyclotomicField p) →+* End family)
    (multiplication_finite : ∀ n : ℕ, 0 < n → IsFinite (n • 𝟙 family).hom.hom.hom.left)
    (multiplication_etale : ∀ n : ℕ, 0 < n → Etale (n • 𝟙 family).hom.hom.hom.left) where
    γ : Fin 3 →
        (AlgebraicClosure (RatFunc (realCyclotomicField p)) ≃ₐ[RatFunc (realCyclotomicField p)]
          AlgebraicClosure (RatFunc (realCyclotomicField p)))
    c : Fin 3 →
        (AlgebraicClosure (RatFunc (realCyclotomicField p)) ≃ₐ[RatFunc (realCyclotomicField p)]
          AlgebraicClosure (RatFunc (realCyclotomicField p)))
    inertia : ∀ i, (Subgroup.zpowers (γ i)).topologicalClosure =
        (![RatFunc.affineInertia (realCyclotomicField p) 0,
           RatFunc.affineInertia (realCyclotomicField p) 1,
           RatFunc.infinityInertia (realCyclotomicField p)] i).map
             (MulAut.conj (c i)).toMonoidHom
    /-- The common orientation and trace label of [DarmonFibres, printed p. 2]. -/
    normalization : ∃ ζ : ℕ → AlgebraicClosure (RatFunc (realCyclotomicField p)),
      ProjectiveLine.HasCommonCuspOrientation (realCyclotomicField p) γ ζ ∧
      ζ p + (ζ p)⁻¹ = algebraMap (realCyclotomicField p) _ (tau p 1)
    realization : PrimePlusTensorTateRealization p family realMultiplication
      multiplication_finite multiplication_etale γ

/-- The auxiliary labelled determinant statement for a specified family and RM action.
This is an explicit arithmetic target, not a field of `PrimePlusFamilyData`.
See [DarmonMestre, Section 4, printed p. 309, display after (6)]; identifying
that display with the specialized family and its labelled torsion requires a
separate same-family comparison. -/
def PrimePlusAuxiliaryDeterminant (p : ℕ) [Fact p.Prime]
    (family : CommGrp (Over (ProjectiveLine.punctured (realCyclotomicField p))))
    (realMultiplication : 𝓞 (realCyclotomicField p) →+* End family) : Prop :=
    ∀ (ell : ℕ) [Fact ell.Prime], 5 ≤ ell → ell ≠ p →
      ∀ (F : Type) [Field F] [Fintype F] [CharP F ell], 3 < Fintype.card F →
        ∀ (φ : 𝓞 (realCyclotomicField p) →+* F), Function.Surjective φ →
          let K := RatFunc (realCyclotomicField p)
          let A := fiber K family (ProjectiveLine.puncturedRationalPoint (realCyclotomicField p))
          let ψ := (fiberEndomorphismMap K family
            (ProjectiveLine.puncturedRationalPoint (realCyclotomicField p))).comp
              realMultiplication
          letI := pointsCoefficientModule K A (𝓞 (realCyclotomicField p)) ψ
          letI : Algebra (𝓞 (realCyclotomicField p)) F := φ.toAlgebra
          letI : Algebra
              (𝓞 (realCyclotomicField p) ⧸
                Ideal.span {(ell : 𝓞 (realCyclotomicField p))}) F :=
            (auxiliaryResidueMap φ).toAlgebra
          let ρ := coefficientTorsionRepresentation K A.X
            (𝓞 (realCyclotomicField p))
            (pointsCoefficientModule_realized K A (𝓞 (realCyclotomicField p)) ψ)
            (ell : 𝓞 (realCyclotomicField p))
          ∃ b : Module.Basis (Fin 2) F
              (F ⊗[𝓞 (realCyclotomicField p) ⧸
                  Ideal.span {(ell : 𝓞 (realCyclotomicField p))}]
                coefficientTorsion K A.X
                (𝓞 (realCyclotomicField p)) (ell : 𝓞 (realCyclotomicField p))),
            ∀ g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
              (LinearMap.toMatrix b b (ρ.baseChange F g)).det =
                (((Field.cyclotomicCharacter K ell g : ℤ_[ell]).toZMod : ZMod ell).val : F)

/-- Data of the explicit plus Jacobian over the three-punctured line. The generic
point and rational fibres refer to this very scheme and this fixed RM action.
No auxiliary determinant, final `p`-adic determinant, residual constituent,
ordinary filtration, comparison, or modularity claim is included. -/
structure PrimePlusFamilyData (p : ℕ) [Fact p.Prime] where
  p_odd : Odd p
  family : CommGrp (Over (ProjectiveLine.punctured (realCyclotomicField p)))
  realMultiplication : 𝓞 (realCyclotomicField p) →+* End family
  realMultiplication_injective : Function.Injective realMultiplication
  proper : IsProper family.X.hom
  smooth : SmoothOfRelativeDimension
    (Module.finrank ℚ (realCyclotomicField p)) family.X.hom
  geometricallyConnected : GeometricallyConnected family.X.hom
  multiplication_finite : ∀ n : ℕ, 0 < n → IsFinite (n • 𝟙 family).hom.hom.hom.left
  multiplication_etale : ∀ n : ℕ, 0 < n → Etale (n • 𝟙 family).hom.hom.hom.left
  multiplication_surjective : ∀ n : ℕ, 0 < n → Surjective (n • 𝟙 family).hom.hom.hom.left
  tensorTateTriple : PrimePlusTensorTateTriple p family realMultiplication
    multiplication_finite multiplication_etale
  rationalTateRank : ∀ (K : Type) [Field K]
      (x : Spec (CommRingCat.of K) ⟶ ProjectiveLine.punctured (realCyclotomicField p)),
      letI : ∀ n : ℕ, IsFinite (p ^ n • 𝟙 family).hom.hom.hom.left :=
        fun n => multiplication_finite (p ^ n) (pow_pos (Fact.out : p.Prime).pos n)
      letI : ∀ n : ℕ, Etale (p ^ n • 𝟙 family).hom.hom.hom.left :=
        fun n => multiplication_etale (p ^ n) (pow_pos (Fact.out : p.Prime).pos n)
      Module.finrank ℚ_[p] (rationalTate K (fiber K family x).X p) =
        Module.finrank ℚ (realCyclotomicField p) * 2
  genericPoint : Additive
    (Over.mk (ProjectiveLine.puncturedRationalPoint (realCyclotomicField p)) ⟶ family.X)
  genericPoint_order : addOrderOf genericPoint = p
  genericJacobian : GroupScheme.PlusCurveJacobian
    (RatFunc (realCyclotomicField p)) p p_odd
    (Hyperelliptic.plusGenericParameter (realCyclotomicField p))
    (fiber (RatFunc (realCyclotomicField p)) family
      (ProjectiveLine.puncturedRationalPoint (realCyclotomicField p)))
  rationalFiberJacobian : ∀ ξ : ProjectiveLine.Parameter (realCyclotomicField p),
    GroupScheme.PlusCurveJacobian (realCyclotomicField p) p p_odd ξ.val
      (fiber (realCyclotomicField p) family
        (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ))

/-- Joint existence of the prime plus family and its labelled geometric data.
The source is [DarmonFibres, Section 3 Example 3 and Propositions 3.2/3.4],
[DarmonRigid, printed pp. 420 and 431, Theorem 2.6(2), proof's last
parenthetical] and [DarmonMestre, Propositions 2.1–2.3]. Their parameters agree by
`s = 2t - 1`. The pointed Abel–Jacobi property fixes this selected family's
generic and nonsingular rational fibres to the displayed plus curve, and its
integral RM acts on those same fibres. The plus infinity trace is `+tau`, as in
[DarmonMestre, Proposition 3.1, proof, printed pp. 308–309]. One roots and path
system supplies the common inertia generators at every prime: apply
[src_milne_lec, Theorem 21.3, printed p. 130, and pp. 131–132] to the same
finite division covers and pass to inverse limits. Naturality preserves RM;
geometric rank-two determinant-one self-duality gives the covariant Tate
convention. Positive finite étale surjective multiplication and rational Tate
rank are the standard characteristic-zero abelian-scheme properties included
in this input. This is a composite literature consequence, not a verbatim
single theorem. It does not identify this choice with `darmonFamily`, remove
an arithmetic twist, or assert the final p-adic determinant or ordinarity.
The exact correspondence of all fields of this joint structure remains subject
to source review; the auxiliary determinant display is not included. -/
theorem exists_primePlusFamilyData (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    Nonempty (PrimePlusFamilyData p) := by
  sorry

/-- The one prime plus family selected from the cited joint existence input. -/
def primePlusData (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) : PrimePlusFamilyData p :=
  Classical.choice (exists_primePlusFamilyData p hp)

/-- The actual prime plus Jacobian family. -/
@[expose] def primePlusFamily (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :=
  (primePlusData p hp).family

/-- The selected generic fibre is the pointed Jacobian of the actual plus curve. -/
def primePlusGenericJacobian (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    GroupScheme.PlusCurveJacobian (RatFunc (realCyclotomicField p)) p
      (primePlusData p hp).p_odd
      (Hyperelliptic.plusGenericParameter (realCyclotomicField p))
      (fiber (RatFunc (realCyclotomicField p)) (primePlusFamily p hp)
        (ProjectiveLine.puncturedRationalPoint (realCyclotomicField p))) :=
  (primePlusData p hp).genericJacobian

/-- Every nonsingular rational fibre is the pointed Jacobian of its plus curve,
with the same family and integral RM action selected at the generic point. -/
def primePlusRationalFiberJacobian (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p)) :
    GroupScheme.PlusCurveJacobian (realCyclotomicField p) p
      (primePlusData p hp).p_odd ξ.val
      (fiber (realCyclotomicField p) (primePlusFamily p hp)
        (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ)) :=
  (primePlusData p hp).rationalFiberJacobian ξ

/-- The fixed integral RM action on the prime plus family. -/
@[expose] def primePlusRealMultiplication (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    𝓞 (realCyclotomicField p) →+* End (primePlusFamily p hp) :=
  (primePlusData p hp).realMultiplication

/-- The selected plus family is proper over its punctured parameter line. -/
instance primePlusFamily_isProper (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    IsProper (primePlusFamily p hp).X.hom :=
  (primePlusData p hp).proper

/-- The selected plus family has the expected relative dimension. -/
instance primePlusFamily_smoothOfRelativeDimension (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    SmoothOfRelativeDimension (Module.finrank ℚ (realCyclotomicField p))
      (primePlusFamily p hp).X.hom :=
  (primePlusData p hp).smooth

/-- Every geometric fibre of the selected plus family is connected. -/
instance primePlusFamily_geometricallyConnected (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    GeometricallyConnected (primePlusFamily p hp).X.hom :=
  (primePlusData p hp).geometricallyConnected

/-- Positive multiplication on the plus family is finite. -/
instance primePlusFamily_multiplication_isFinite (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (n : ℕ) [NeZero n] : IsFinite (n • 𝟙 (primePlusFamily p hp)).hom.hom.hom.left :=
  (primePlusData p hp).multiplication_finite n (NeZero.pos n)

/-- Positive multiplication on the plus family is étale. -/
instance primePlusFamily_multiplication_etale (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (n : ℕ) [NeZero n] : Etale (n • 𝟙 (primePlusFamily p hp)).hom.hom.hom.left :=
  (primePlusData p hp).multiplication_etale n (NeZero.pos n)

/-- Positive multiplication on the plus family is surjective. -/
instance primePlusFamily_multiplication_surjective (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (n : ℕ) [NeZero n] : Surjective (n • 𝟙 (primePlusFamily p hp)).hom.hom.hom.left :=
  (primePlusData p hp).multiplication_surjective n (NeZero.pos n)

end HilbertModularity.Hypergeometric
