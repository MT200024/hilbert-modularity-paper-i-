/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.Pullback
public import HilbertModularity.Geometry.Etale.Algebra
public import HilbertModularity.FieldTheory.Etale.Galois
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation

/-! # Finite étale field covers detect arithmetic automorphisms

Finite separable extensions give actual spectrum covers. Their geometric
points detect every absolute Galois automorphism in characteristic zero.
-/

public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u
variable (K : Type u) [Field K]

/-- Finite separable spectrum covers detect every absolute Galois automorphism. -/
theorem galoisToEtaleFundamentalGroup_injective [CharZero K] :
    Function.Injective (galoisToEtaleFundamentalGroup K (𝟙 (Spec (CommRingCat.of K)))) := by
  apply PreGaloisCategory.toAut_injective_of_non_trivial
  intro g hg
  apply AlgEquiv.ext
  intro a
  let L := IntermediateField.adjoin K ({a} : Set (AlgebraicClosure K))
  let : FiniteDimensional K L :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral a)
  let : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
  let : Module.FinitePresentation K L := Module.finitePresentation_of_finite K L
  let : Algebra.Etale K L := {}
  let A := CommAlgCat.FiniteEtale.of K L
  exact finiteEtaleAlgebraPoint_fixed K A L.val g
    (hg (finiteEtaleAlgebraCover K A) (finiteEtaleAlgebraPoint K A L.val))
    (IntermediateField.AdjoinSimple.gen K a)

/-- The arithmetic Galois group embeds as a closed subgroup of the actual
finite étale fibre-automorphism group over the field. -/
theorem galoisToEtaleFundamentalGroup_isClosedEmbedding [CharZero K] :
    Topology.IsClosedEmbedding
      (galoisToEtaleFundamentalGroup K (𝟙 (Spec (CommRingCat.of K)))) :=
  (continuous_galoisToEtaleFundamentalGroup K _).isClosedEmbedding
    (galoisToEtaleFundamentalGroup_injective K)

/-- For a scheme with a rational point over the field, the actual arithmetic
homomorphism is injective: the structure map detects its field-cover action. -/
theorem galoisToEtaleFundamentalGroup_injective_of_section [CharZero K]
    {S : Scheme.{u}} (f : S ⟶ Spec (CommRingCat.of K))
    (x : Spec (CommRingCat.of K) ⟶ S) (hx : x ≫ f = 𝟙 _) :
    Function.Injective (galoisToEtaleFundamentalGroup K x) := by
  intro g h he
  have hm := congrArg (etaleFundamentalGroupMap f K x) he
  rw [etaleFundamentalGroupMap_galois, etaleFundamentalGroupMap_galois] at hm
  have hi : Function.Injective (galoisToEtaleFundamentalGroup K (x ≫ f)) := by
    rw [hx]
    exact galoisToEtaleFundamentalGroup_injective K
  exact hi hm

/-- A rational point embeds the arithmetic Galois group as an actual closed
subgroup of the geometric fibre-automorphism group. -/
theorem galoisToEtaleFundamentalGroup_isClosedEmbedding_of_section [CharZero K]
    {S : Scheme.{u}} (f : S ⟶ Spec (CommRingCat.of K))
    (x : Spec (CommRingCat.of K) ⟶ S) (hx : x ≫ f = 𝟙 _) :
    Topology.IsClosedEmbedding (galoisToEtaleFundamentalGroup K x) :=
  (continuous_galoisToEtaleFundamentalGroup K x).isClosedEmbedding
    (galoisToEtaleFundamentalGroup_injective_of_section K f x hx)

/-- Restriction of the arithmetic action to algebra fibres is postcomposition. -/
theorem algebraFiberAut_galois_apply
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (A : CommAlgCat.FiniteEtale.{u} K) (φ : A.obj →ₐ[K] AlgebraicClosure K) :
    (algebraFiberAut K (galoisToEtaleFundamentalGroup K (𝟙 (Spec (CommRingCat.of K))) g)).hom.app
      (Opposite.op A) φ = g.toAlgHom.comp φ := by
  apply (finiteEtaleAlgebraPointEquiv K A).injective
  change finiteEtaleAlgebraPointEquiv K A
      ((finiteEtaleAlgebraPointEquiv K A).symm (g • finiteEtaleAlgebraPoint K A φ)) = _
  rw [Equiv.apply_symm_apply]
  exact finiteEtaleAlgebraPoint_smul K A φ g

/-- Reconstructing the arithmetic action recovers the original absolute Galois automorphism. -/
theorem reconstructedGalois_algebraFiberAut_galois [CharZero K]
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    CommAlgCat.FiniteEtale.reconstructedGalois K
      (algebraFiberAut K (galoisToEtaleFundamentalGroup K (𝟙 (Spec (CommRingCat.of K))) g)) = g := by
  apply AlgEquiv.ext
  intro a
  let L := IntermediateField.adjoin K ({a} : Set (AlgebraicClosure K))
  let : FiniteDimensional K L :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral a)
  rw [show a = ((IntermediateField.AdjoinSimple.gen K a : L) : AlgebraicClosure K) from rfl,
    CommAlgCat.FiniteEtale.reconstructedGalois_apply]
  exact congrArg (fun φ : L →ₐ[K] AlgebraicClosure K => φ (IntermediateField.AdjoinSimple.gen K a))
    (algebraFiberAut_galois_apply K g (CommAlgCat.FiniteEtale.ofIntermediateField K L) L.val)

/-- Every natural automorphism of geometric fibres over a characteristic-zero field
comes from its absolute Galois group. -/
theorem galoisToEtaleFundamentalGroup_surjective [CharZero K] :
    Function.Surjective (galoisToEtaleFundamentalGroup K (𝟙 (Spec (CommRingCat.of K)))) := by
  intro σ
  refine ⟨CommAlgCat.FiniteEtale.reconstructedGalois K (algebraFiberAut K σ), ?_⟩
  apply algebraFiberAut_injective K
  apply CommAlgCat.FiniteEtale.reconstructedGalois_injective K
  exact reconstructedGalois_algebraFiberAut_galois K _

/-- The absolute Galois group is the actual étale fundamental group of the
spectrum of a characteristic-zero field, as a topological group. -/
def galoisEtaleFundamentalGroupEquiv [CharZero K] :
    (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) ≃ₜ*
      etaleFundamentalGroup K (𝟙 (Spec (CommRingCat.of K))) :=
  let e := MulEquiv.ofBijective
    (galoisToEtaleFundamentalGroup K (𝟙 (Spec (CommRingCat.of K))))
    ⟨galoisToEtaleFundamentalGroup_injective K, galoisToEtaleFundamentalGroup_surjective K⟩
  { e with
    continuous_toFun := continuous_galoisToEtaleFundamentalGroup K _
    continuous_invFun := Continuous.continuous_symm_of_equiv_compact_to_t2
      (f := e.toEquiv) (continuous_galoisToEtaleFundamentalGroup K _) }

/-- The field fundamental-group equivalence acts by the arithmetic Galois action. -/
@[simp] theorem galoisEtaleFundamentalGroupEquiv_apply [CharZero K]
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    galoisEtaleFundamentalGroupEquiv K g =
      galoisToEtaleFundamentalGroup K (𝟙 (Spec (CommRingCat.of K))) g := by
  rfl

end AlgebraicGeometry.Scheme
