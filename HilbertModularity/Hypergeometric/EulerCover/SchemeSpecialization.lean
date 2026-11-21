/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.EulerCover.SchemeBaseChange
public import HilbertModularity.Hypergeometric.EulerCover.Specialization
import HilbertModularity.Geometry.ProjectiveNaturality

/-! # Scheme fibres of the affine Euler family

Evaluation at a parameter with `t` and `1 - t` invertible gives a point of the
actual punctured parameter scheme. The fibre of the affine Euler family at this
point is the Euler cover with parameter `t`; the comparison is the standard
affine tensor-product pullback of
[TripathiGoswamiRevised, Definition 2.3].
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
attribute [local instance] MvPolynomial.gradedAlgebra

namespace HilbertModularity.Hypergeometric.EulerCover

universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- The point of the actual punctured parameter line defined by evaluation at
`t`; the two unit hypotheses make this a map from its localized coordinate ring. -/
def puncturedParameterPoint (t : S) (ht : IsUnit t) (h1t : IsUnit (1 - t)) :
    Spec (CommRingCat.of S) ⟶ ProjectiveLine.punctured R :=
  Spec.map (CommRingCat.ofHom (parameterEval R t ht h1t)) ≫
    (ProjectiveLine.puncturedAffineIso R).inv

/-- The punctured parameter point retains the original coefficient map. -/
theorem puncturedParameterPoint_toSpec (t : S) (ht : IsUnit t)
    (h1t : IsUnit (1 - t)) :
    puncturedParameterPoint R S t ht h1t ≫ ProjectiveLine.puncturedToSpec R =
      Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  rw [puncturedParameterPoint, Category.assoc,
    ProjectiveLine.puncturedAffineIso_inv_toSpec, ← Spec.map_comp]
  congr 1
  ext r
  exact parameterEval_coeff R t ht h1t r

/-- In the standard projective chart, the evaluated parameter point has
affine coordinate `t`. -/
theorem puncturedParameterPoint_inclusion (t : S) (ht : IsUnit t)
    (h1t : IsUnit (1 - t)) :
    puncturedParameterPoint R S t ht h1t ≫ ProjectiveLine.puncturedInclusion R =
      Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom (algebraMap R S) t)) ≫
        ProjectiveLine.chartMap R 0 1 (by decide) := by
  rw [puncturedParameterPoint, Category.assoc,
    ProjectiveLine.puncturedAffineIso_inv_inclusion, ← Category.assoc,
    ← Spec.map_comp]
  have h : (parameterEval R t ht h1t).comp
      (algebraMap (Polynomial R) (ProjectiveLine.puncturedCoordinateRing R)) =
        Polynomial.eval₂RingHom (algebraMap R S) t := by
    apply RingHom.ext
    intro p
    exact parameterEval_algebraMap R t ht h1t p
  rw [← CommRingCat.ofHom_comp, h]

private theorem affinePoint_eq_chartMap_eval
    (K : Type u) [Field K] (t : K) :
    ProjectiveLine.affinePoint K t =
      Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom (RingHom.id K) t)) ≫
        ProjectiveLine.chartMap K 0 1 (by decide) := by
  let f := ProjectiveLine.parameterSections K t
  have hX : f (MvPolynomial.X 1) = 1 := by
    simp [f, ProjectiveLine.parameterSections]
  have htop : (Spec (CommRingCat.of K)).basicOpen (f (MvPolynomial.X 1)) = ⊤ := by
    rw [hX]
    exact Scheme.basicOpen_of_isUnit (Spec (CommRingCat.of K)) isUnit_one
  have h := Proj.basicOpen_ι_fromOfGlobalSections
    (MvPolynomial.homogeneousSubmodule (Fin 2) K) f
    (ProjectiveLine.parameterSections_irrelevant K t)
    (by decide : 0 < 1) (MvPolynomial.isHomogeneous_X K (1 : Fin 2))
  let e : Spec (CommRingCat.of K) ⟶
      ((Spec (CommRingCat.of K)).basicOpen (f (MvPolynomial.X 1))).toScheme :=
    (Spec (CommRingCat.of K)).topIso.inv ≫
      ((Spec (CommRingCat.of K)).isoOfEq htop).inv
  have he : e ≫
      ((Spec (CommRingCat.of K)).basicOpen (f (MvPolynomial.X 1))).ι = 𝟙 _ := by
    dsimp [e]
    rw [Category.assoc, Scheme.isoOfEq_inv_ι, Scheme.toIso_inv_ι]
  have hpoint : ProjectiveLine.affinePoint K t =
      e ≫ Proj.toBasicOpenOfGlobalSections
        (MvPolynomial.homogeneousSubmodule (Fin 2) K) f rfl
        (by decide : 0 < 1) (MvPolynomial.isHomogeneous_X K (1 : Fin 2)) ≫
          (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) K)
            (MvPolynomial.X 1)).ι := by
    have h' := congrArg (fun q => e ≫ q) h
    rw [← Category.assoc, he, Category.id_comp] at h'
    exact h'
  rw [hpoint]
  simp only [ProjectiveLine.chartMap, Proj.fromSpecOfUnit, Proj.awayι,
    Proj.toBasicOpenOfGlobalSections]
  let x : Γ(Spec (CommRingCat.of K), ⊤) := f (MvPolynomial.X 1)
  let q : Spec (CommRingCat.of K) ⟶
      Spec (CommRingCat.of (Localization.Away x)) :=
    e ≫ ((Spec (CommRingCat.of K)).isoOfEq
      ((Spec (CommRingCat.of K)).toSpecΓ_preimage_basicOpen x)).inv ≫
      (Spec (CommRingCat.of K)).toSpecΓ ∣_ PrimeSpectrum.basicOpen x ≫
        (basicOpenIsoSpecAway x).hom
  have hqbase : q ≫ Spec.map (CommRingCat.ofHom
      (algebraMap (Γ(Spec (CommRingCat.of K), ⊤)) (Localization.Away x))) =
        (Spec (CommRingCat.of K)).toSpecΓ := by
    have hr := morphismRestrict_ι
      ((Spec (CommRingCat.of K)).toSpecΓ) (PrimeSpectrum.basicOpen x)
    dsimp [q]
    simp only [Category.assoc, basicOpenIsoSpecAway_hom_SpecMap]
    rw [hr]
    simp only [← Category.assoc, Scheme.isoOfEq_inv_ι]
    change (e ≫ ((Spec (CommRingCat.of K)).basicOpen
      (f (MvPolynomial.X 1))).ι) ≫ _ = _
    rw [he, Category.id_comp]
  have hu : IsUnit (f (MvPolynomial.X 1)) := by rw [hX]; exact isUnit_one
  have hf : f = (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.comp
      ((Polynomial.eval₂RingHom (RingHom.id K) t).comp
        (ProjectiveLine.chartCoordinates K 0)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [f, ProjectiveLine.parameterSections, ProjectiveLine.chartCoordinates]
    · intro i
      fin_cases i <;>
        simp [f, ProjectiveLine.parameterSections, ProjectiveLine.chartCoordinates]
  have hhom : Proj.homogeneousEvaluation
      (MvPolynomial.homogeneousSubmodule (Fin 2) K) f (MvPolynomial.X 1) hu =
        (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.comp
          ((Polynomial.eval₂RingHom (RingHom.id K) t).comp
            (ProjectiveLine.chartEvaluation K 0 1 (by decide))) := by
    have hunit : IsUnit
        (ProjectiveLine.chartCoordinates K 0 (MvPolynomial.X 1)) := by
      simp [ProjectiveLine.chartCoordinates]
    have hcomp := Proj.homogeneousEvaluation_comp
      (MvPolynomial.homogeneousSubmodule (Fin 2) K)
      (ProjectiveLine.chartCoordinates K 0)
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.comp
        (Polynomial.eval₂RingHom (RingHom.id K) t))
      (MvPolynomial.X 1) hunit
    simpa only [← hf, ProjectiveLine.chartEvaluation, RingHom.comp_assoc] using hcomp
  have hmap :
      (Localization.awayMap f (MvPolynomial.X 1)).comp
        (algebraMap (ProjectiveLine.ChartRing K 1)
          (Localization.Away (MvPolynomial.X 1))) =
      (algebraMap (Γ(Spec (CommRingCat.of K), ⊤)) (Localization.Away x)).comp
        (Proj.homogeneousEvaluation
          (MvPolynomial.homogeneousSubmodule (Fin 2) K) f (MvPolynomial.X 1) hu) := by
    unfold Proj.homogeneousEvaluation
    have haway : Localization.awayMap f (MvPolynomial.X (1 : Fin 2) :
        MvPolynomial (Fin 2) K) =
        (algebraMap (Γ(Spec (CommRingCat.of K), ⊤)) (Localization.Away x)).comp
          (Localization.awayLift f (MvPolynomial.X (1 : Fin 2) :
            MvPolynomial (Fin 2) K) hu) := by
      apply IsLocalization.ringHom_ext
        (M := Submonoid.powers (MvPolynomial.X (1 : Fin 2) :
          MvPolynomial (Fin 2) K))
      apply RingHom.ext
      intro a
      simp only [RingHom.comp_apply, Localization.awayMap,
        IsLocalization.Away.map, IsLocalization.map_eq, Localization.awayLift,
        IsLocalization.Away.lift_eq]
      rfl
    rw [haway, RingHom.comp_assoc]
  simp only [Proj.toBasicOpenOfGlobalSections] at *
  unfold Localization.awayMap at hmap
  unfold IsLocalization.Away.map at hmap
  rw [hmap]
  rw [hhom]
  simp only [← RingHom.comp_assoc, CommRingCat.ofHom_comp, Spec.map_comp,
    Category.assoc]
  simp only [← Category.assoc]
  dsimp only [q] at hqbase
  simp only [← Category.assoc] at hqbase
  rw [hqbase]
  change (((((Spec (CommRingCat.of K)).toSpecΓ ≫
    Spec.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv) ≫ _) ≫ _) ≫ _) ≫ _ = _
  rw [toSpecΓ_SpecMap_ΓSpecIso_inv, Category.id_comp]
  simp only [ProjectiveLine.chartEvaluation, Category.assoc]
  rfl

/-- For a field parameter away from zero and one, evaluation of the punctured
coordinate ring gives the existing projective-line parameter point. -/
theorem puncturedParameterPoint_eq_puncturedPoint
    (K : Type u) [Field K] (ξ : ProjectiveLine.Parameter K)
    (ht : IsUnit ξ.val) (h1t : IsUnit (1 - ξ.val)) :
    puncturedParameterPoint K K ξ.val ht h1t =
      ProjectiveLine.puncturedPoint K ξ := by
  apply (cancel_mono (ProjectiveLine.puncturedInclusion K)).mp
  rw [puncturedParameterPoint_inclusion, ProjectiveLine.puncturedPoint_inclusion]
  exact (affinePoint_eq_chartMap_eval K ξ.val).symm

/-- The affine Euler family specialized along the genuine parameter-point map. -/
def affineFamilySpecialization (N m : ℕ) (t : S) (ht : IsUnit t)
    (h1t : IsUnit (1 - t)) :
    affineScheme N m t ⟶ affineFamily R N m :=
  Spec.map (CommRingCat.ofHom (familyCoverSpecializationMap R N m t ht h1t))

private theorem coverBaseChangeEquiv_includeRight_transport
    {P : Type u} [CommRing P] [Algebra P S] (τ : P) (s : S)
    (h : algebraMap P S τ = s) (N m : ℕ) (a : CoverRing N m τ) :
    (h ▸ coverBaseChangeEquiv (R := P) (S := S) N m τ)
        ((Algebra.TensorProduct.includeRight :
          CoverRing N m τ →ₐ[P] S ⊗[P] CoverRing N m τ) a) =
      (h ▸ coverRingMap (algebraMap P S) N m τ) a := by
  cases h
  exact coverTensorMap_includeRight (R := P) (S := S) N m τ a

/-- Before passing through the punctured-line chart, the fibre is the usual
affine tensor-product pullback of the cover and parameter evaluation. -/
def affineFamilyAffineFibreIso (N m : ℕ) (t : S) (ht : IsUnit t)
    (h1t : IsUnit (1 - t)) :
    affineScheme N m t ≅
      pullback (Spec.map (CommRingCat.ofHom (parameterEval R t ht h1t)))
        (structureMap N m (familyParameter R)) := by
  let : Algebra (ProjectiveLine.puncturedCoordinateRing R) S :=
    (parameterEval R t ht h1t).toAlgebra
  have heval : algebraMap (ProjectiveLine.puncturedCoordinateRing R) S
      (familyParameter R) = t := parameterEval_familyParameter R t ht h1t
  exact Scheme.Spec.mapIso
      (familyCoverSpecializationEquiv R N m t heval).toRingEquiv.toCommRingCatIso.op ≪≫
    (pullbackSpecIso (ProjectiveLine.puncturedCoordinateRing R) S
      (CoverRing N m (familyParameter R))).symm

/-- The affine pullback comparison projects to the coefficient scheme by the
actual specialized structural morphism. -/
theorem affineFamilyAffineFibreIso_fst (N m : ℕ) (t : S) (ht : IsUnit t)
    (h1t : IsUnit (1 - t)) :
    (affineFamilyAffineFibreIso R S N m t ht h1t).hom ≫
        pullback.fst (Spec.map (CommRingCat.ofHom (parameterEval R t ht h1t)))
          (structureMap N m (familyParameter R)) = structureMap N m t := by
  let : Algebra (ProjectiveLine.puncturedCoordinateRing R) S :=
    (parameterEval R t ht h1t).toAlgebra
  have heval : algebraMap (ProjectiveLine.puncturedCoordinateRing R) S
      (familyParameter R) = t := parameterEval_familyParameter R t ht h1t
  change Spec.map (CommRingCat.ofHom
      (familyCoverSpecializationEquiv R N m t heval).toRingHom) ≫
      (pullbackSpecIso (ProjectiveLine.puncturedCoordinateRing R) S
        (CoverRing N m (familyParameter R))).inv ≫
        pullback.fst (Spec.map (CommRingCat.ofHom
          (algebraMap (ProjectiveLine.puncturedCoordinateRing R) S)))
          (Spec.map (CommRingCat.ofHom
            (algebraMap (ProjectiveLine.puncturedCoordinateRing R)
              (CoverRing N m (familyParameter R))))) = _
  rw [pullbackSpecIso_inv_fst', ← Spec.map_comp]
  congr 1
  ext s
  exact (familyCoverSpecializationEquiv R N m t heval).commutes s

/-- The affine pullback comparison's family projection is specialization of
the actual root algebra, including its covering coordinate. -/
theorem affineFamilyAffineFibreIso_snd (N m : ℕ) (t : S) (ht : IsUnit t)
    (h1t : IsUnit (1 - t)) :
    (affineFamilyAffineFibreIso R S N m t ht h1t).hom ≫
        pullback.snd (Spec.map (CommRingCat.ofHom (parameterEval R t ht h1t)))
          (structureMap N m (familyParameter R)) =
      affineFamilySpecialization R S N m t ht h1t := by
  let : Algebra (ProjectiveLine.puncturedCoordinateRing R) S :=
    (parameterEval R t ht h1t).toAlgebra
  have heval : algebraMap (ProjectiveLine.puncturedCoordinateRing R) S
      (familyParameter R) = t := parameterEval_familyParameter R t ht h1t
  change Spec.map (CommRingCat.ofHom
      (familyCoverSpecializationEquiv R N m t heval).toRingHom) ≫
      (pullbackSpecIso (ProjectiveLine.puncturedCoordinateRing R) S
        (CoverRing N m (familyParameter R))).inv ≫
        pullback.snd (Spec.map (CommRingCat.ofHom
          (algebraMap (ProjectiveLine.puncturedCoordinateRing R) S)))
          (Spec.map (CommRingCat.ofHom
            (algebraMap (ProjectiveLine.puncturedCoordinateRing R)
              (CoverRing N m (familyParameter R))))) = _
  rw [pullbackSpecIso_inv_snd, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change (familyCoverSpecializationEquiv R N m t heval)
      ((Algebra.TensorProduct.includeRight :
        CoverRing N m (familyParameter R) →ₐ[ProjectiveLine.puncturedCoordinateRing R]
          S ⊗[ProjectiveLine.puncturedCoordinateRing R]
            CoverRing N m (familyParameter R)) a) =
      familyCoverSpecializationMap R N m t ht h1t a
  change (heval ▸ coverBaseChangeEquiv
      (R := ProjectiveLine.puncturedCoordinateRing R) (S := S) N m (familyParameter R))
        ((Algebra.TensorProduct.includeRight :
          CoverRing N m (familyParameter R) →ₐ[ProjectiveLine.puncturedCoordinateRing R]
            S ⊗[ProjectiveLine.puncturedCoordinateRing R]
              CoverRing N m (familyParameter R)) a) =
    (heval ▸ coverRingMap
      (algebraMap (ProjectiveLine.puncturedCoordinateRing R) S) N m
      (familyParameter R)) a
  exact coverBaseChangeEquiv_includeRight_transport S (familyParameter R) t heval N m a

/-- The comparison from the affine chart pullback to the fibre over the actual
punctured parameter scheme changes only the base chart. -/
def affineChartFibreIso (N m : ℕ) (t : S) (ht : IsUnit t)
    (h1t : IsUnit (1 - t)) :
    pullback (Spec.map (CommRingCat.ofHom (parameterEval R t ht h1t)))
      (structureMap N m (familyParameter R)) ≅
        pullback (puncturedParameterPoint R S t ht h1t)
          (familyStructureMap R N m) := by
  let f := Spec.map (CommRingCat.ofHom (parameterEval R t ht h1t))
  let g : affineFamily R N m ⟶
      Spec (CommRingCat.of (ProjectiveLine.puncturedCoordinateRing R)) :=
    structureMap N m (familyParameter R)
  let p := puncturedParameterPoint R S t ht h1t
  let q := familyStructureMap R N m
  let i := (ProjectiveLine.puncturedAffineIso R).inv
  have h₁ : f ≫ i = (𝟙 _) ≫ p := by
    simp [f, i, p, puncturedParameterPoint]
  have h₂ : g ≫ i = (𝟙 _) ≫ q := by
    change g ≫ i = g ≫ i
    rfl
  have h₁' : p ≫ (ProjectiveLine.puncturedAffineIso R).hom = (𝟙 _) ≫ f := by
    change (f ≫ (ProjectiveLine.puncturedAffineIso R).inv) ≫
      (ProjectiveLine.puncturedAffineIso R).hom = f
    simp
  have h₂' : q ≫ (ProjectiveLine.puncturedAffineIso R).hom = (𝟙 _) ≫ g := by
    change (g ≫ (ProjectiveLine.puncturedAffineIso R).inv) ≫
      (ProjectiveLine.puncturedAffineIso R).hom = g
    simp
  let φ := pullback.map f g p q (𝟙 _) (𝟙 _) i h₁ h₂
  let ψ := pullback.map p q f g (𝟙 _) (𝟙 _)
    (ProjectiveLine.puncturedAffineIso R).hom h₁' h₂'
  have hφ₁ : φ ≫ pullback.fst p q = pullback.fst f g := by
    change (pullback.lift (pullback.fst f g ≫ 𝟙 _)
      (pullback.snd f g ≫ 𝟙 _) _) ≫ pullback.fst p q = _
    simp only [pullback.lift_fst, Category.comp_id]
  have hφ₂ : φ ≫ pullback.snd p q = pullback.snd f g := by
    change (pullback.lift (pullback.fst f g ≫ 𝟙 _)
      (pullback.snd f g ≫ 𝟙 _) _) ≫ pullback.snd p q = _
    simp only [pullback.lift_snd, Category.comp_id]
  have hψ₁ : ψ ≫ pullback.fst f g = pullback.fst p q := by
    change (pullback.lift (pullback.fst p q ≫ 𝟙 _)
      (pullback.snd p q ≫ 𝟙 _) _) ≫ pullback.fst f g = _
    simp only [pullback.lift_fst, Category.comp_id]
  have hψ₂ : ψ ≫ pullback.snd f g = pullback.snd p q := by
    change (pullback.lift (pullback.fst p q ≫ 𝟙 _)
      (pullback.snd p q ≫ 𝟙 _) _) ≫ pullback.snd f g = _
    simp only [pullback.lift_snd, Category.comp_id]
  refine ⟨φ, ψ, ?_, ?_⟩
  · apply pullback.hom_ext
    · change (φ ≫ ψ) ≫ pullback.fst f g = 𝟙 _ ≫ pullback.fst f g
      simp only [Category.assoc, hψ₁, hφ₁, Category.id_comp]
    · change (φ ≫ ψ) ≫ pullback.snd f g = 𝟙 _ ≫ pullback.snd f g
      simp only [Category.assoc, hψ₂, hφ₂, Category.id_comp]
  · apply pullback.hom_ext
    · change (ψ ≫ φ) ≫ pullback.fst p q = 𝟙 _ ≫ pullback.fst p q
      simp only [Category.assoc, hφ₁, hψ₁, Category.id_comp]
    · change (ψ ≫ φ) ≫ pullback.snd p q = 𝟙 _ ≫ pullback.snd p q
      simp only [Category.assoc, hφ₂, hψ₂, Category.id_comp]

/-- Changing from the affine chart to the punctured parameter scheme preserves
the coefficient projection of the pullback. -/
theorem affineChartFibreIso_hom_fst (N m : ℕ) (t : S) (ht : IsUnit t)
    (h1t : IsUnit (1 - t)) :
    (affineChartFibreIso R S N m t ht h1t).hom ≫
        pullback.fst (puncturedParameterPoint R S t ht h1t)
          (familyStructureMap R N m) =
      pullback.fst (Spec.map (CommRingCat.ofHom (parameterEval R t ht h1t)))
        (structureMap N m (familyParameter R)) := by
  let f := Spec.map (CommRingCat.ofHom (parameterEval R t ht h1t))
  let g : affineFamily R N m ⟶
      Spec (CommRingCat.of (ProjectiveLine.puncturedCoordinateRing R)) :=
    structureMap N m (familyParameter R)
  let p := puncturedParameterPoint R S t ht h1t
  let q := familyStructureMap R N m
  change (pullback.lift (pullback.fst f g ≫ 𝟙 _)
    (pullback.snd f g ≫ 𝟙 _) _) ≫ pullback.fst p q = _
  simp only [pullback.lift_fst, Category.comp_id]
  rfl

/-- Changing from the affine chart to the punctured parameter scheme preserves
the family projection of the pullback. -/
theorem affineChartFibreIso_hom_snd (N m : ℕ) (t : S) (ht : IsUnit t)
    (h1t : IsUnit (1 - t)) :
    (affineChartFibreIso R S N m t ht h1t).hom ≫
        pullback.snd (puncturedParameterPoint R S t ht h1t)
          (familyStructureMap R N m) =
      pullback.snd (Spec.map (CommRingCat.ofHom (parameterEval R t ht h1t)))
        (structureMap N m (familyParameter R)) := by
  let f := Spec.map (CommRingCat.ofHom (parameterEval R t ht h1t))
  let g : affineFamily R N m ⟶
      Spec (CommRingCat.of (ProjectiveLine.puncturedCoordinateRing R)) :=
    structureMap N m (familyParameter R)
  let p := puncturedParameterPoint R S t ht h1t
  let q := familyStructureMap R N m
  change (pullback.lift (pullback.fst f g ≫ 𝟙 _)
    (pullback.snd f g ≫ 𝟙 _) _) ≫ pullback.snd p q = _
  simp only [pullback.lift_snd, Category.comp_id]
  rfl

/-- The actual family fibre at a legitimate punctured parameter point is the
Euler cover at that parameter. -/
def affineFamilyFibreIso (N m : ℕ) (t : S) (ht : IsUnit t)
    (h1t : IsUnit (1 - t)) :
    affineScheme N m t ≅
      pullback (puncturedParameterPoint R S t ht h1t)
        (familyStructureMap R N m) :=
  affineFamilyAffineFibreIso R S N m t ht h1t ≪≫
    affineChartFibreIso R S N m t ht h1t

/-- The actual fibre's first projection is the Euler scheme's coefficient map. -/
theorem affineFamilyFibreIso_fst (N m : ℕ) (t : S) (ht : IsUnit t)
    (h1t : IsUnit (1 - t)) :
    (affineFamilyFibreIso R S N m t ht h1t).hom ≫
        pullback.fst (puncturedParameterPoint R S t ht h1t)
          (familyStructureMap R N m) = structureMap N m t := by
  rw [affineFamilyFibreIso, Iso.trans_hom, Category.assoc,
    affineChartFibreIso_hom_fst]
  exact affineFamilyAffineFibreIso_fst R S N m t ht h1t

/-- The actual fibre's second projection is the root-algebra specialization map. -/
theorem affineFamilyFibreIso_snd (N m : ℕ) (t : S) (ht : IsUnit t)
    (h1t : IsUnit (1 - t)) :
    (affineFamilyFibreIso R S N m t ht h1t).hom ≫
        pullback.snd (puncturedParameterPoint R S t ht h1t)
          (familyStructureMap R N m) =
      affineFamilySpecialization R S N m t ht h1t := by
  rw [affineFamilyFibreIso, Iso.trans_hom, Category.assoc,
    affineChartFibreIso_hom_snd]
  exact affineFamilyAffineFibreIso_snd R S N m t ht h1t

/-- Specialization intertwines the family deck action with the deck action
at the evaluated parameter. -/
theorem affineFamilySpecialization_deck (N : ℕ) [NeZero N] (m : ℕ)
    (t : S) (ht : IsUnit t) (h1t : IsUnit (1 - t))
    (ζ : rootsOfUnity N (ProjectiveLine.puncturedCoordinateRing R)) :
    affineFamilySpecialization R S N m t ht h1t ≫
        (deckTransformation N m (familyParameter R) ζ).hom =
      (deckTransformation N m t
        (rootsOfUnity.mapHom N (parameterEval R t ht h1t) ζ)).hom ≫
          affineFamilySpecialization R S N m t ht h1t := by
  rw [affineFamilySpecialization, deckTransformation_hom, deckTransformation_hom]
  erw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact congrArg CommRingCat.ofHom
    (familyCoverSpecializationMap_deck R N m t ht h1t ζ)

/-- Deck transformations of the affine family preserve its map to the actual
punctured parameter line. -/
theorem familyDeckTransformation_structureMap (N : ℕ) [NeZero N] (m : ℕ)
    (ζ : rootsOfUnity N (ProjectiveLine.puncturedCoordinateRing R)) :
    (deckTransformation N m (familyParameter R) ζ).hom ≫
        familyStructureMap R N m = familyStructureMap R N m := by
  change (deckTransformation N m (familyParameter R) ζ).hom ≫
    (structureMap N m (familyParameter R) ≫
      (ProjectiveLine.puncturedAffineIso R).inv) =
        structureMap N m (familyParameter R) ≫
          (ProjectiveLine.puncturedAffineIso R).inv
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun k => k ≫ (ProjectiveLine.puncturedAffineIso R).inv)
      (deckTransformation_structureMap N m (familyParameter R) ζ))

/-- The family deck automorphism as an isomorphism over the actual punctured
parameter line. -/
def familyDeckOverIso (N : ℕ) [NeZero N] (m : ℕ)
    (ζ : rootsOfUnity N (ProjectiveLine.puncturedCoordinateRing R)) :
    Over.mk (familyStructureMap R N m) ≅ Over.mk (familyStructureMap R N m) :=
  Over.isoMk (deckTransformation N m (familyParameter R) ζ)
    (familyDeckTransformation_structureMap R N m ζ)

/-- The actual family deck transformation pulled back to a parameter fibre. -/
def affineFamilyPullbackDeckTransformation (N : ℕ) [NeZero N] (m : ℕ)
    (t : S) (ht : IsUnit t) (h1t : IsUnit (1 - t))
    (ζ : rootsOfUnity N (ProjectiveLine.puncturedCoordinateRing R)) :
    pullback (puncturedParameterPoint R S t ht h1t) (familyStructureMap R N m) ≅
      pullback (puncturedParameterPoint R S t ht h1t) (familyStructureMap R N m) :=
  pullbackSymmetry _ _ ≪≫
    ((Over.pullback (puncturedParameterPoint R S t ht h1t) ⋙
      Over.forget (Spec (CommRingCat.of S))).mapIso
        (familyDeckOverIso R N m ζ)) ≪≫
      (pullbackSymmetry _ _).symm

/-- The pulled-back deck action fixes the fibre's coefficient projection. -/
theorem affineFamilyPullbackDeckTransformation_fst (N : ℕ) [NeZero N] (m : ℕ)
    (t : S) (ht : IsUnit t) (h1t : IsUnit (1 - t))
    (ζ : rootsOfUnity N (ProjectiveLine.puncturedCoordinateRing R)) :
    (affineFamilyPullbackDeckTransformation R S N m t ht h1t ζ).hom ≫
        pullback.fst (puncturedParameterPoint R S t ht h1t)
          (familyStructureMap R N m) =
      pullback.fst (puncturedParameterPoint R S t ht h1t)
        (familyStructureMap R N m) := by
  let f := puncturedParameterPoint R S t ht h1t
  let g := familyStructureMap R N m
  let d := ((Over.pullback f).map (familyDeckOverIso R N m ζ).hom).left
  change (pullbackSymmetry f g).hom ≫ d ≫
      (pullbackSymmetry f g).inv ≫ pullback.fst f g = pullback.fst f g
  rw [pullbackSymmetry_inv_comp_fst]
  have hd : d ≫ pullback.snd g f = pullback.snd g f := by
    change (pullback.lift
      (pullback.fst g f ≫ (deckTransformation N m (familyParameter R) ζ).hom)
      (pullback.snd g f) _) ≫ pullback.snd g f = _
    exact pullback.lift_snd _ _ _
  rw [hd, pullbackSymmetry_hom_comp_snd]

/-- The other fibre projection carries the original family deck action. -/
theorem affineFamilyPullbackDeckTransformation_snd (N : ℕ) [NeZero N] (m : ℕ)
    (t : S) (ht : IsUnit t) (h1t : IsUnit (1 - t))
    (ζ : rootsOfUnity N (ProjectiveLine.puncturedCoordinateRing R)) :
    (affineFamilyPullbackDeckTransformation R S N m t ht h1t ζ).hom ≫
        pullback.snd (puncturedParameterPoint R S t ht h1t)
          (familyStructureMap R N m) =
      pullback.snd (puncturedParameterPoint R S t ht h1t)
        (familyStructureMap R N m) ≫
          (deckTransformation N m (familyParameter R) ζ).hom := by
  let f := puncturedParameterPoint R S t ht h1t
  let g := familyStructureMap R N m
  let d := ((Over.pullback f).map (familyDeckOverIso R N m ζ).hom).left
  change (pullbackSymmetry f g).hom ≫ d ≫
      (pullbackSymmetry f g).inv ≫ pullback.snd f g =
        pullback.snd f g ≫ (deckTransformation N m (familyParameter R) ζ).hom
  rw [pullbackSymmetry_inv_comp_snd]
  have hd : d ≫ pullback.fst g f =
      pullback.fst g f ≫ (deckTransformation N m (familyParameter R) ζ).hom := by
    change (pullback.lift
      (pullback.fst g f ≫ (deckTransformation N m (familyParameter R) ζ).hom)
      (pullback.snd g f) _) ≫ pullback.fst g f = _
    exact pullback.lift_fst _ _ _
  rw [hd]
  simpa only [affineFamily, Category.assoc] using
    congrArg (fun k => k ≫ (deckTransformation N m (familyParameter R) ζ).hom)
      (pullbackSymmetry_hom_comp_fst f g)

/-- The family-fibre comparison transports the actual deck action, including
the mapped root of unity, through the genuine parameter fibre. -/
theorem affineFamilyFibreIso_deck (N : ℕ) [NeZero N] (m : ℕ)
    (t : S) (ht : IsUnit t) (h1t : IsUnit (1 - t))
    (ζ : rootsOfUnity N (ProjectiveLine.puncturedCoordinateRing R)) :
    (affineFamilyFibreIso R S N m t ht h1t).hom ≫
        (affineFamilyPullbackDeckTransformation R S N m t ht h1t ζ).hom =
      (deckTransformation N m t
        (rootsOfUnity.mapHom N (parameterEval R t ht h1t) ζ)).hom ≫
          (affineFamilyFibreIso R S N m t ht h1t).hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, affineFamilyPullbackDeckTransformation_fst,
      affineFamilyFibreIso_fst, Category.assoc,
      affineFamilyFibreIso_fst, deckTransformation_structureMap]
  · let F := (affineFamilyFibreIso R S N m t ht h1t).hom
    let D := (affineFamilyPullbackDeckTransformation R S N m t ht h1t ζ).hom
    let s := pullback.snd (puncturedParameterPoint R S t ht h1t)
      (familyStructureMap R N m)
    let a := affineFamilySpecialization R S N m t ht h1t
    let d := (deckTransformation N m (familyParameter R) ζ).hom
    let d' := (deckTransformation N m t
      (rootsOfUnity.mapHom N (parameterEval R t ht h1t) ζ)).hom
    have hs : D ≫ s = s ≫ d :=
      affineFamilyPullbackDeckTransformation_snd R S N m t ht h1t ζ
    have hf : F ≫ s = a := affineFamilyFibreIso_snd R S N m t ht h1t
    have hd : a ≫ d = d' ≫ a :=
      affineFamilySpecialization_deck R S N m t ht h1t ζ
    have hstep : F ≫ (D ≫ s) = F ≫ (s ≫ d) :=
      congrArg (fun k => F ≫ k) hs
    have hleft : (F ≫ D) ≫ s = a ≫ d :=
      (Category.assoc F D s).trans
        (hstep.trans ((Category.assoc F s d).symm.trans
          (congrArg (fun k => k ≫ d) hf)))
    have hright : d' ≫ a = (d' ≫ F) ≫ s :=
      (congrArg (fun k => d' ≫ k) hf.symm).trans
        (Category.assoc d' F s).symm
    change (F ≫ D) ≫ s = (d' ≫ F) ≫ s
    exact hleft.trans (hd.trans hright)

end HilbertModularity.Hypergeometric.EulerCover
