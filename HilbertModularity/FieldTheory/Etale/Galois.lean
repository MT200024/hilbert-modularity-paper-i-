/- Assembled by AxiomProver. -/

module

public import Mathlib.RingTheory.Etale.Finite
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.FieldTheory.IntermediateField.Algebraic
public import Mathlib.CategoryTheory.Galois.Topology

/-! # Reconstructing field automorphisms from finite étale fibres

The action on embeddings of finite subextensions is compatible with their
inclusions. It therefore assembles to an automorphism of the algebraic closure.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace CommAlgCat.FiniteEtale

universe u
variable (K : Type u) [Field K] [CharZero K]

/-- A finite subextension of the algebraic closure is a finite étale algebra. -/
def ofIntermediateField (L : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K L] :
    CommAlgCat.FiniteEtale.{u} K := by
  letI : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
  letI : Module.FinitePresentation K L := Module.finitePresentation_of_finite K L
  letI : Algebra.Etale K L := {}
  exact CommAlgCat.FiniteEtale.of K L

variable (α : Aut (fiber K (AlgebraicClosure K)))

/-- The image of the inclusion of a finite subfield under a natural fibre automorphism. -/
def fieldEmbedding (L : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K L] :
    L →ₐ[K] AlgebraicClosure K :=
  α.hom.app (op (ofIntermediateField K L)) L.val

/-- The embeddings supplied by a natural automorphism agree on nested subfields. -/
theorem fieldEmbedding_comp_inclusion
    {L M : IntermediateField K (AlgebraicClosure K)} [FiniteDimensional K L]
    [FiniteDimensional K M] (h : L ≤ M) :
    (fieldEmbedding K α M).comp (IntermediateField.inclusion h) = fieldEmbedding K α L := by
  let f : ofIntermediateField K L ⟶ ofIntermediateField K M :=
    ObjectProperty.homMk (CommAlgCat.ofHom (IntermediateField.inclusion h))
  have he := ConcreteCategory.congr_hom (α.hom.naturality f.op) M.val
  change fieldEmbedding K α L =
    (fieldEmbedding K α M).comp (IntermediateField.inclusion h) at he
  exact he.symm

/-- The value at an algebraic element obtained from its finite simple subextension. -/
def fieldMap (a : AlgebraicClosure K) : AlgebraicClosure K :=
  letI := IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (R := K) a)
  fieldEmbedding K α (IntermediateField.adjoin K {a}) (IntermediateField.AdjoinSimple.gen K a)

/-- The reconstructed value can be computed in any finite subextension containing the element. -/
theorem fieldMap_eq (L : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K L]
    (a : L) : fieldMap K α (a : AlgebraicClosure K) = fieldEmbedding K α L a := by
  let := IntermediateField.adjoin.finiteDimensional
    (Algebra.IsIntegral.isIntegral (R := K) (a : AlgebraicClosure K))
  have h : IntermediateField.adjoin K ({(a : AlgebraicClosure K)} : Set (AlgebraicClosure K)) ≤ L :=
    IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr a.property)
  exact (DFunLike.congr_fun (fieldEmbedding_comp_inclusion K α h)
    (IntermediateField.AdjoinSimple.gen K (a : AlgebraicClosure K))).symm

/-- The reconstructed map fixes the base field. -/
theorem fieldMap_algebraMap (a : K) :
    fieldMap K α (algebraMap K (AlgebraicClosure K) a) = algebraMap K (AlgebraicClosure K) a := by
  let L : IntermediateField K (AlgebraicClosure K) := ⊥
  exact (fieldMap_eq K α L (algebraMap K L a)).trans ((fieldEmbedding K α L).commutes a)

/-- Compatibility on a joint finite subextension gives additivity. -/
theorem fieldMap_add (a b : AlgebraicClosure K) :
    fieldMap K α (a + b) = fieldMap K α a + fieldMap K α b := by
  let L := IntermediateField.adjoin K ({a, b} : Set (AlgebraicClosure K))
  let : FiniteDimensional K L := IntermediateField.finiteDimensional_adjoin_pair
    (Algebra.IsIntegral.isIntegral a) (Algebra.IsIntegral.isIntegral b)
  let a' : L := ⟨a, IntermediateField.subset_adjoin K _ (by simp)⟩
  let b' : L := ⟨b, IntermediateField.subset_adjoin K _ (by simp)⟩
  calc
    fieldMap K α (a + b) = fieldEmbedding K α L (a' + b') := fieldMap_eq K α L (a' + b')
    _ = fieldEmbedding K α L a' + fieldEmbedding K α L b' := map_add _ _ _
    _ = fieldMap K α a + fieldMap K α b := by rw [← fieldMap_eq, ← fieldMap_eq]

/-- Compatibility on a joint finite subextension gives multiplicativity. -/
theorem fieldMap_mul (a b : AlgebraicClosure K) :
    fieldMap K α (a * b) = fieldMap K α a * fieldMap K α b := by
  let L := IntermediateField.adjoin K ({a, b} : Set (AlgebraicClosure K))
  let : FiniteDimensional K L := IntermediateField.finiteDimensional_adjoin_pair
    (Algebra.IsIntegral.isIntegral a) (Algebra.IsIntegral.isIntegral b)
  let a' : L := ⟨a, IntermediateField.subset_adjoin K _ (by simp)⟩
  let b' : L := ⟨b, IntermediateField.subset_adjoin K _ (by simp)⟩
  calc
    fieldMap K α (a * b) = fieldEmbedding K α L (a' * b') := fieldMap_eq K α L (a' * b')
    _ = fieldEmbedding K α L a' * fieldEmbedding K α L b' := map_mul _ _ _
    _ = fieldMap K α a * fieldMap K α b := by rw [← fieldMap_eq, ← fieldMap_eq]

/-- The compatible finite-subextension actions form an actual algebra homomorphism. -/
def reconstructedAlgHom : AlgebraicClosure K →ₐ[K] AlgebraicClosure K where
  toFun := fieldMap K α
  map_zero' := by simpa only [map_zero] using fieldMap_algebraMap K α 0
  map_one' := by simpa only [map_one] using fieldMap_algebraMap K α 1
  map_add' := fieldMap_add K α
  map_mul' := fieldMap_mul K α
  commutes' := fieldMap_algebraMap K α

/-- The reconstructed algebra endomorphism is an automorphism by normality of the algebraic closure. -/
def reconstructedGalois : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K :=
  AlgEquiv.ofBijective (reconstructedAlgHom K α)
    (AlgHom.normal_bijective K (AlgebraicClosure K) (AlgebraicClosure K) (reconstructedAlgHom K α))

/-- On every finite subextension, reconstruction recovers the original action on its inclusion. -/
theorem reconstructedGalois_apply (L : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K L] (a : L) :
    reconstructedGalois K α (a : AlgebraicClosure K) = fieldEmbedding K α L a :=
  fieldMap_eq K α L a

/-- Reconstruction recovers the natural automorphism on every finite étale algebra embedding. -/
theorem reconstructedGalois_comp (A : CommAlgCat.FiniteEtale.{u} K)
    (φ : A.obj →ₐ[K] AlgebraicClosure K) :
    (reconstructedGalois K α).toAlgHom.comp φ = α.hom.app (op A) φ := by
  have hS : φ.range.IsAlgebraic := fun a _ => Algebra.IsAlgebraic.isAlgebraic a
  let L := hS.toIntermediateField
  let : FiniteDimensional K L := φ.toLinearMap.finiteDimensional_range
  let ψ : A.obj →ₐ[K] L := φ.codRestrict L.toSubalgebra (fun a => ⟨a, rfl⟩)
  let f : A ⟶ ofIntermediateField K L := ObjectProperty.homMk (CommAlgCat.ofHom ψ)
  have h := ConcreteCategory.congr_hom (α.hom.naturality f.op) L.val
  change α.hom.app (op A) (L.val.comp ψ) = (fieldEmbedding K α L).comp ψ at h
  change α.hom.app (op A) φ = (fieldEmbedding K α L).comp ψ at h
  rw [h]
  ext a
  exact reconstructedGalois_apply K α L (ψ a)

/-- A natural automorphism of the algebraic fibre functor is determined by its reconstructed
field automorphism. -/
theorem reconstructedGalois_injective : Function.Injective (reconstructedGalois K) := by
  intro α β h
  apply Iso.ext
  apply NatTrans.ext
  funext A
  apply FintypeCat.hom_ext
  intro φ
  exact (reconstructedGalois_comp K α A.unop φ).symm.trans
    ((congrArg (fun g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K =>
      g.toAlgHom.comp φ) h).trans (reconstructedGalois_comp K β A.unop φ))

end CommAlgCat.FiniteEtale
