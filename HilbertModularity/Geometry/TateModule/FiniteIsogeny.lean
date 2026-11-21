/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.TateModule.Isogeny
public import HilbertModularity.Geometry.FinitePointLifting

/-! # Finite geometric kernels and Tate isogenies

The kernel of the actual geometric point map of a finite group-scheme morphism
embeds into its geometric fibre above the identity. Finiteness is therefore
a consequence of the scheme morphism, rather than a separate point-group
assumption, in the Tate isogeny comparison of [TripathiGoswami].
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GroupScheme

universe u

variable (K : Type u) [Field K]
  {A B : Over (Spec (CommRingCat.of K))}
  [GrpObj A] [GrpObj B]
  (f : A ⟶ B) [IsMonHom f] [IsFinite f.left]

/-- A finite group-scheme morphism has finite kernel on actual geometric points. -/
instance finite_pointsMap_ker : Finite (pointsMap K (AlgebraicClosure K) f).ker := by
  let z := (0 : Points K (AlgebraicClosure K) B).toMul.left
  let F := Over.mk z ⟶ Over.mk f.left
  let : Finite F := Scheme.RationalPoint.finite_geometricFiber (AlgebraicClosure K) f.left z
  let i : (pointsMap K (AlgebraicClosure K) f).ker → F := fun x =>
    Over.homMk x.val.toMul.left
      (congrArg (fun y : Points K (AlgebraicClosure K) B => y.toMul.left) x.property)
  apply Finite.of_injective i
  intro x y h
  apply Subtype.ext
  change x.val.toMul = y.val.toMul
  apply Over.OverMorphism.ext
  exact congrArg (fun q : F => q.left) h

/-- A finite surjective group-scheme morphism is surjective on actual geometric points. -/
theorem pointsMap_surjective_of_finite_surjective [Surjective f.left] :
    Function.Surjective (pointsMap K (AlgebraicClosure K) f) := by
  intro b
  obtain ⟨a, ha⟩ := Scheme.RationalPoint.over_postcomp_surjective (AlgebraicClosure K)
    (fieldPoint K (AlgebraicClosure K)).hom f b.toMul
  exact ⟨Additive.ofMul a, congrArg Additive.ofMul ha⟩

variable [IsCommMonObj A] [IsCommMonObj B] (p : ℕ) [Fact p.Prime]

/-- A finite group-scheme morphism acts injectively on the actual integral Tate module. -/
theorem integralTateMap_injective_of_isFinite : Function.Injective (integralTateMap K p f) :=
  integralTateMap_injective_of_finite_kernel K p f

/-- A finite morphism surjective on geometric points preserves the rational Galois Tate representation. -/
def finiteTateIsogenyEquiv
    (hf : Function.Surjective (pointsMap K (AlgebraicClosure K) f)) :
    (tateRepresentation K A p).Equiv (tateRepresentation K B p) :=
  tateIsogenyEquiv K p f hf

/-- A finite surjective group-scheme morphism preserves the actual rational Galois Tate representation. -/
def tateFiniteSurjectiveEquiv [Surjective f.left] :
    (tateRepresentation K A p).Equiv (tateRepresentation K B p) :=
  finiteTateIsogenyEquiv K f p (pointsMap_surjective_of_finite_surjective K f)

end AlgebraicGeometry.GroupScheme
