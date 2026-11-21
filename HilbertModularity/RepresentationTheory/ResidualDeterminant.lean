/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.ScalarRestriction
public import HilbertModularity.NumberTheory.LocalSpecialization.Quotient
public import HilbertModularity.NumberTheory.LocalSpecialization.Completion
public import Mathlib.Algebra.Module.Lattice
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.Charpoly.BaseChange

/-! # Determinants of integral and residual lattice representations

A stable lattice in a fraction-field representation recovers the original
representation after extending scalars. Its residual representation is the
scalar extension of that actual lattice to the residue field. Determinants
therefore specialize compatibly. This supplies the integral-lattice step in
[TripathiGoswami, determinant rigidity]; existence of the compatible RM
system and arithmetic Frobenius density remain separate inputs.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Representation

variable {R G M : Type*} [CommRing R] [Monoid G] [AddCommGroup M] [Module R M]

/-- The ideal multiple of a representation is a stable submodule. -/
def idealMultipleSubrepresentation (ρ : Representation R G M) (I : Ideal R) : Subrepresentation ρ where
  toSubmodule := I • ⊤
  apply_mem_toSubmodule g v hv := by
    refine Submodule.smul_induction_on (p := fun v => ρ g v ∈ (I • ⊤ : Submodule R M)) hv ?_ ?_
    · intro r hr n hn
      rw [map_smul]
      exact Submodule.smul_mem_smul hr (Submodule.mem_top : ρ g n ∈ (⊤ : Submodule R M))
    · intro x y hx hy
      rw [map_add]
      exact Submodule.add_mem _ hx hy

/-- Tensor reduction of a representation is equivariantly its quotient by the ideal multiple. -/
def residualQuotientEquiv (ρ : Representation R G M) (I : Ideal R) :
    ((ρ.baseChange (R ⧸ I)).restrictScalars R).Equiv
      (ρ.quotient (I • ⊤) (idealMultipleSubrepresentation ρ I).apply_mem_toSubmodule) :=
  .mk (TensorProduct.quotTensorEquivQuotSMul M I) (by
    intro g
    apply LinearMap.ext
    intro v
    induction v using TensorProduct.inductionOn with
    | tmul r v =>
      induction r using Quotient.inductionOn with
      | h r =>
        change TensorProduct.quotTensorEquivQuotSMul M I
          (Ideal.Quotient.mk I r ⊗ₜ[R] ρ g v) =
            (ρ.quotient (I • ⊤) (idealMultipleSubrepresentation ρ I).apply_mem_toSubmodule) g
              (TensorProduct.quotTensorEquivQuotSMul M I (Ideal.Quotient.mk I r ⊗ₜ[R] v))
        rw [TensorProduct.quotTensorEquivQuotSMul_mk_tmul,
          TensorProduct.quotTensorEquivQuotSMul_mk_tmul]
        change (Submodule.Quotient.mk (r • ρ g v) : M ⧸ (I • ⊤)) =
          Submodule.Quotient.mk (ρ g (r • v))
        rw [map_smul]
    | add x y hx hy => simp only [map_add, hx, hy])

end Representation

namespace Submodule

variable {R K V ι : Type*} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
  (M : Submodule R V) [IsLattice K M] (b : Module.Basis ι R M)

/-- Extending a full lattice to the fraction field recovers its ambient vector space. -/
def latticeScalarExtensionEquiv : (K ⊗[R] M) ≃ₗ[K] V := by
  let e := (b.baseChange K).equiv (b.extendOfIsLattice K) (Equiv.refl _)
  have he : e.toLinearMap = M.subtype.liftBaseChange K := by
    apply (b.baseChange K).ext
    intro i
    change e (b.baseChange K i) = M.subtype.liftBaseChange K (b.baseChange K i)
    simp only [e, Module.Basis.equiv_apply, Equiv.refl_apply]
    simp [Module.Basis.baseChange_apply]
  exact LinearEquiv.ofBijective (M.subtype.liftBaseChange K) (he ▸ e.bijective)

@[simp]
theorem latticeScalarExtensionEquiv_tmul (c : K) (v : M) :
    latticeScalarExtensionEquiv M b (c ⊗ₜ[R] v) = c • (v : V) := rfl

end Submodule

namespace Representation

variable {R K G V ι : Type*} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
  [Monoid G] [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
  (ρ : Representation K G V) (S : Subrepresentation (ρ.restrictScalars R))
  [Submodule.IsLattice K S.toSubmodule] (b : Module.Basis ι R S.toSubmodule)

/-- A stable lattice recovers the original representation equivariantly over the fraction field. -/
def latticeScalarExtensionEquiv : (S.toRepresentation.baseChange K).Equiv ρ :=
  .mk (S.toSubmodule.latticeScalarExtensionEquiv b) (by
    intro g
    apply LinearMap.ext
    intro v
    induction v using TensorProduct.inductionOn with
    | tmul c v =>
      change c • ρ g (v : V) = ρ g (c • (v : V))
      exact (ρ g).map_smul c v |>.symm
    | add x y hx hy => simp only [map_add, hx, hy])

include b in
/-- The characteristic-zero determinant is the image of the determinant on a full stable lattice. -/
theorem det_latticeScalarExtension (g : G) :
    LinearMap.det (ρ g) = algebraMap R K (LinearMap.det (S.toRepresentation g)) := by
  let : Module.Free R S.toSubmodule := Module.Free.of_basis b
  let e := latticeScalarExtensionEquiv ρ S b
  have he : e.toLinearEquiv.toLinearMap ∘ₗ (S.toRepresentation g).baseChange K ∘ₗ
      e.toLinearEquiv.symm.toLinearMap = ρ g := by
    apply LinearMap.ext
    intro v
    change e ((S.toRepresentation.baseChange K) g (e.symm v)) = ρ g v
    simpa using e.toIntertwiningMap.isIntertwining (S.toRepresentation.baseChange K) ρ g (e.symm v)
  rw [← he, LinearMap.det_conj, LinearMap.det_baseChange]

include b in
omit [IsFractionRing R K] in
/-- Reduction of a stable lattice specializes its integral determinant. -/
theorem det_latticeReduction (k : Type*) [CommRing k] [Algebra R k] (g : G) :
    LinearMap.det ((S.toRepresentation.baseChange k) g) =
      algebraMap R k (LinearMap.det (S.toRepresentation g)) := by
  let : Module.Free R S.toSubmodule := Module.Free.of_basis b
  exact LinearMap.det_baseChange (S.toRepresentation g)

include b in
/-- One integral determinant simultaneously realizes the characteristic-zero and residual values. -/
theorem exists_integral_lattice_determinant (k : Type*) [CommRing k] [Algebra R k] (g : G) :
    ∃ d : R, algebraMap R K d = LinearMap.det (ρ g) ∧
      algebraMap R k d = LinearMap.det ((S.toRepresentation.baseChange k) g) :=
  ⟨LinearMap.det (S.toRepresentation g),
    (det_latticeScalarExtension ρ S b g).symm, (det_latticeReduction ρ S b k g).symm⟩

variable {κ : Type*} (T : Subrepresentation (ρ.restrictScalars R))
  [Submodule.IsLattice K T.toSubmodule] (c : Module.Basis κ R T.toSubmodule)

include b c in
/-- The integral determinant is independent of the choice of full stable lattice. -/
theorem det_lattice_independent (g : G) :
    LinearMap.det (S.toRepresentation g) = LinearMap.det (T.toRepresentation g) := by
  apply IsFractionRing.injective R K
  rw [← det_latticeScalarExtension ρ S b g, ← det_latticeScalarExtension ρ T c g]

include b c in
/-- Residual determinants agree for any two full stable lattices. -/
theorem det_latticeReduction_independent (k : Type*) [CommRing k] [Algebra R k] (g : G) :
    LinearMap.det ((S.toRepresentation.baseChange k) g) =
      LinearMap.det ((T.toRepresentation.baseChange k) g) := by
  rw [det_latticeReduction ρ S b k g, det_latticeReduction ρ T c k g,
    det_lattice_independent ρ S b T c g]

end Representation

namespace IsDedekindDomain.HeightOneSpectrum

variable {R K G V ι : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K] [Monoid G]
  [AddCommGroup V] [Module K V] (P : HeightOneSpectrum R)
  [Module (P.valuationSubringAtPrime K) V] [IsScalarTower (P.valuationSubringAtPrime K) K V]
  (ρ : Representation K G V)
  (S : Subrepresentation (ρ.restrictScalars (P.valuationSubringAtPrime K)))
  [Submodule.IsLattice K S.toSubmodule]
  (b : Module.Basis ι (P.valuationSubringAtPrime K) S.toSubmodule)

include b in
/-- The determinant of an actual local stable lattice reduces to the specialized characteristic-zero determinant. -/
theorem specialization_det_lattice (g : G) :
    let : Algebra (P.valuationSubringAtPrime K) (R ⧸ P.asIdeal) := P.localResidue.toAlgebra
    ∃ hd : P.valuation K (LinearMap.det (ρ g)) ≤ 1,
      P.specialization (LinearMap.det (ρ g)) hd =
        LinearMap.det ((S.toRepresentation.baseChange (R ⧸ P.asIdeal)) g) := by
  let : Algebra (P.valuationSubringAtPrime K) (R ⧸ P.asIdeal) := P.localResidue.toAlgebra
  let d : P.valuationSubringAtPrime K := LinearMap.det (S.toRepresentation g)
  have he : LinearMap.det (ρ g) = (d : K) := Representation.det_latticeScalarExtension ρ S b g
  have hd : P.valuation K (LinearMap.det (ρ g)) ≤ 1 := by
    rw [he]
    change (d : K) ∈ (P.valuation K).valuationSubring
    rw [← P.valuationSubringAtPrime_eq_valuationSubring]
    exact d.property
  refine ⟨hd, ?_⟩
  have hl : P.localElement (LinearMap.det (ρ g)) hd = d := Subtype.ext he
  rw [specialization, hl]
  exact (Representation.det_latticeReduction ρ S b (R ⧸ P.asIdeal) g).symm

include b in
/-- Equality of a residual lattice determinant with a local unit gives a determinant ratio of residue one. -/
theorem determinant_ratio_specialization (g : G) (y : K) (hy : P.valuation K y = 1) :
    let : Algebra (P.valuationSubringAtPrime K) (R ⧸ P.asIdeal) := P.localResidue.toAlgebra
    LinearMap.det ((S.toRepresentation.baseChange (R ⧸ P.asIdeal)) g) =
        P.specialization y hy.le →
      ∃ hratio : P.valuation K (LinearMap.det (ρ g) / y) ≤ 1,
        P.specialization (LinearMap.det (ρ g) / y) hratio = 1 := by
  let : Algebra (P.valuationSubringAtPrime K) (R ⧸ P.asIdeal) := P.localResidue.toAlgebra
  dsimp only
  intro hres
  obtain ⟨hd, hdet⟩ := P.specialization_det_lattice ρ S b g
  exact P.specialization_div_eq_one (LinearMap.det (ρ g)) y hd hy (hdet.trans hres)

end IsDedekindDomain.HeightOneSpectrum

namespace IsDedekindDomain.HeightOneSpectrum

variable {R K G V ι : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K] [Monoid G]
  (P : HeightOneSpectrum R) [AddCommGroup V] [Module (P.adicCompletion K) V]
  [Module (P.adicCompletionIntegers K) V]
  [IsScalarTower (P.adicCompletionIntegers K) (P.adicCompletion K) V]
  (ρ : Representation (P.adicCompletion K) G V)
  (S : Subrepresentation (ρ.restrictScalars (P.adicCompletionIntegers K)))
  [Submodule.IsLattice (P.adicCompletion K) S.toSubmodule]
  (b : Module.Basis ι (P.adicCompletionIntegers K) S.toSubmodule)

include b in
/-- A common algebraic determinant reduces compatibly with a stable lattice in the actual completion. -/
theorem completion_specialization_det_lattice (g : G) (x : K)
    (hx : LinearMap.det (ρ g) = algebraMap K (P.adicCompletion K) x) :
    ∃ hint : P.valuation K x ≤ 1,
      P.completionResidueMap (P.specialization x hint) =
        LinearMap.det ((S.toRepresentation.baseChange
          (IsLocalRing.ResidueField (P.adicCompletionIntegers K))) g) := by
  let d : P.adicCompletionIntegers K := LinearMap.det (S.toRepresentation g)
  have he : (d : P.adicCompletion K) = algebraMap K (P.adicCompletion K) x :=
    (Representation.det_latticeScalarExtension ρ S b g).symm.trans hx
  have hint : P.valuation K x ≤ 1 := by
    rw [← adicCompletion.valued_coe]
    change Valued.v (algebraMap K (P.adicCompletion K) x) ≤ 1
    rw [← he]
    exact d.property
  refine ⟨hint, ?_⟩
  have hd : P.completionIntegralMap (P.localElement x hint) = d := Subtype.ext he.symm
  rw [P.completionResidueMap_specialization, hd]
  exact (Representation.det_latticeReduction ρ S b
    (IsLocalRing.ResidueField (P.adicCompletionIntegers K)) g).symm

include b in
/-- A residual determinant congruence in the completion reflects to a residue-one algebraic ratio. -/
theorem completion_determinant_ratio_specialization (g : G) (x y : K)
    (hx : LinearMap.det (ρ g) = algebraMap K (P.adicCompletion K) x)
    (hy : P.valuation K y = 1)
    (hres : LinearMap.det ((S.toRepresentation.baseChange
        (IsLocalRing.ResidueField (P.adicCompletionIntegers K))) g) =
      P.completionResidueMap (P.specialization y hy.le)) :
    ∃ hratio : P.valuation K (x / y) ≤ 1,
      P.specialization (x / y) hratio = 1 := by
  obtain ⟨hint, hdet⟩ := P.completion_specialization_det_lattice ρ S b g x hx
  apply P.specialization_div_eq_one x y hint hy
  exact P.completionResidueMap_injective (hdet.trans hres)

end IsDedekindDomain.HeightOneSpectrum
