/- Assembled by AxiomProver. -/

module

public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.Matrix.Nonsingular
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.RepresentationTheory.Basic

/-! # Homology of the two-component dual graph

The multigraph with two vertices and `d + 1` parallel edges has an actual
integral incidence complex. Its first homology is explicitly free of rank `d`.
This is the graph-theoretic input to [TripathiGoswami, corrected stable model].
-/

@[expose] public noncomputable section

open scoped BigOperators
open CategoryTheory

namespace Graph

/-- The two-component multigraph with one edge for each of the `d + 1` nodes. -/
def twoComponent (d : ℕ) : Graph Bool (Fin (d + 1)) :=
  Graph.banana false true Set.univ

/-- Every node connects the two distinct components. -/
theorem twoComponent_isLink (d : ℕ) (e : Fin (d + 1)) :
    (twoComponent d).IsLink e false true := by
  simp [twoComponent, banana_isLink]

/-- The oriented incidence boundary sends every edge from the first component to the second. -/
def twoComponentBoundary (R : Type*) [CommRing R] (d : ℕ) :
    (Fin (d + 1) → R) →ₗ[R] (Bool → R) where
  toFun x v := if v then ∑ i, x i else -(∑ i, x i)
  map_add' x y := by
    funext v
    cases v <;> simp [Finset.sum_add_distrib, add_comm]
  map_smul' a x := by
    funext v
    cases v <;> simp [Finset.mul_sum]

/-- The boundary of a single oriented edge is the difference of its endpoint vertices. -/
theorem twoComponentBoundary_single (R : Type*) [CommRing R] (d : ℕ)
    (e : Fin (d + 1)) (a : R) :
    twoComponentBoundary R d (Pi.single e a) = Pi.single true a - Pi.single false a := by
  ext v
  cases v <;> simp [twoComponentBoundary]

/-- A one-chain is a cycle exactly when the sum of its edge coefficients vanishes. -/
theorem mem_ker_twoComponentBoundary_iff
    (R : Type*) [CommRing R] (d : ℕ) (x : Fin (d + 1) → R) :
    x ∈ (twoComponentBoundary R d).ker ↔ ∑ i, x i = 0 := by
  constructor
  · intro hx
    have h := congrFun (LinearMap.mem_ker.mp hx) true
    simpa [twoComponentBoundary] using h
  · intro hx
    apply LinearMap.mem_ker.mpr
    funext v
    cases v <;> simp [twoComponentBoundary, hx]

/-- Dropping the first edge gives explicit coordinates on the cycle module. The omitted
coefficient is minus the sum of the remaining coefficients. -/
def twoComponentCycleEquiv (R : Type*) [CommRing R] (d : ℕ) :
    (twoComponentBoundary R d).ker ≃ₗ[R] (Fin d → R) where
  toFun x i := x.1 i.succ
  invFun y := ⟨Fin.cons (-(∑ i, y i)) y,
    (mem_ker_twoComponentBoundary_iff R d _).mpr (by simp [Fin.sum_univ_succ])⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero]
      have hx := (mem_ker_twoComponentBoundary_iff R d x).mp x.property
      rw [Fin.sum_univ_succ] at hx
      exact (eq_neg_of_add_eq_zero_left hx).symm
    · simp
  right_inv y := by funext i; simp
  map_add' x y := rfl
  map_smul' a x := rfl

/-- The incidence short complex has zero two-chains, edge one-chains and vertex zero-chains. -/
def twoComponentComplex (R : Type*) [CommRing R] (d : ℕ) :
    ShortComplex (ModuleCat R) :=
  ShortComplex.mk (0 : ModuleCat.of R (Fin 0 → R) ⟶ ModuleCat.of R (Fin (d + 1) → R))
    (ModuleCat.ofHom (twoComponentBoundary R d)) (by simp)

/-- The actual first homology of the incidence complex is the explicit cycle module. -/
def twoComponentHomologyEquivCycles (R : Type*) [CommRing R] (d : ℕ) :
    (twoComponentComplex R d).homology ≃ₗ[R] (twoComponentBoundary R d).ker :=
  (((twoComponentComplex R d).asIsoHomologyπ rfl).symm ≪≫
    (twoComponentComplex R d).moduleCatCyclesIso).toLinearEquiv

/-- The actual first homology has one free coordinate for every edge after the first. -/
def twoComponentHomologyEquiv (R : Type*) [CommRing R] (d : ℕ) :
    (twoComponentComplex R d).homology ≃ₗ[R] (Fin d → R) :=
  (twoComponentHomologyEquivCycles R d).trans (twoComponentCycleEquiv R d)

/-- The explicit integral cycles give a basis, not merely a numerical Euler characteristic. -/
def twoComponentHomologyBasis (R : Type*) [CommRing R] (d : ℕ) :
    Module.Basis (Fin d) R (twoComponentComplex R d).homology :=
  (Pi.basisFun R (Fin d)).map (twoComponentHomologyEquiv R d).symm

/-- The actual graph homology is a free module. -/
instance free_twoComponentHomology (R : Type*) [CommRing R] (d : ℕ) :
    Module.Free R (twoComponentComplex R d).homology :=
  Module.Free.of_basis (twoComponentHomologyBasis R d)

/-- The graph homology is finitely generated. -/
instance finite_twoComponentHomology (R : Type*) [CommRing R] (d : ℕ) :
    Module.Finite R (twoComponentComplex R d).homology :=
  Module.Finite.of_basis (twoComponentHomologyBasis R d)

/-- In particular, the integral first homology has rank `d`. -/
theorem finrank_twoComponentHomology (d : ℕ) :
    Module.finrank ℤ (twoComponentComplex ℤ d).homology = d := by
  rw [(twoComponentHomologyEquiv ℤ d).finrank_eq]
  exact Module.finrank_fin_fun ℤ

/-- Permuting the nodes while fixing the two components induces a genuine chain map. -/
def twoComponentPermutationMap (R : Type*) [CommRing R] (d : ℕ)
    (e : Equiv.Perm (Fin (d + 1))) : twoComponentComplex R d ⟶ twoComponentComplex R d where
  τ₁ := 𝟙 _
  τ₂ := ModuleCat.ofHom (LinearEquiv.funCongrLeft R R e.symm).toLinearMap
  τ₃ := 𝟙 _
  comm₁₂ := by simp [twoComponentComplex]
  comm₂₃ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (Fin (d + 1) → R) at x
    funext v
    change (if v then ∑ i, x (e.symm i) else -(∑ i, x (e.symm i))) =
      (if v then ∑ i, x i else -(∑ i, x i))
    rw [Equiv.sum_comp e.symm x]

/-- Fixing every node makes the induced chain map the identity. -/
theorem twoComponentPermutationMap_eq_id (R : Type*) [CommRing R] (d : ℕ)
    (e : Equiv.Perm (Fin (d + 1))) (he : ∀ i, e i = i) :
    twoComponentPermutationMap R d e = 𝟙 (twoComponentComplex R d) := by
  have he' : e = Equiv.refl _ := Equiv.ext he
  subst e
  ext <;> rfl

/-- The node permutation acts on the actual homology through the homology functor. -/
def twoComponentHomologyMap (R : Type*) [CommRing R] (d : ℕ)
    (e : Equiv.Perm (Fin (d + 1))) :
    Module.End R (twoComponentComplex R d).homology :=
  (ShortComplex.homologyMap (twoComponentPermutationMap R d e)).hom

/-- If residue Galois fixes the nodes and the two individual branches, its induced
map on the actual integral graph homology is the identity. -/
theorem twoComponentHomologyMap_eq_id (R : Type*) [CommRing R] (d : ℕ)
    (e : Equiv.Perm (Fin (d + 1))) (he : ∀ i, e i = i) :
    twoComponentHomologyMap R d e = LinearMap.id := by
  unfold twoComponentHomologyMap
  rw [twoComponentPermutationMap_eq_id R d e he, ShortComplex.homologyMap_id]
  rfl

/-- Composition of node permutations gives the corresponding composition of chain maps. -/
theorem twoComponentPermutationMap_mul (R : Type*) [CommRing R] (d : ℕ)
    (e f : Equiv.Perm (Fin (d + 1))) :
    twoComponentPermutationMap R d (e * f) =
      twoComponentPermutationMap R d f ≫ twoComponentPermutationMap R d e := by
  apply ShortComplex.Hom.ext
  · rfl
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (Fin (d + 1) → R) at x
    funext i
    rfl
  · rfl

/-- The induced homology maps respect multiplication of node permutations. -/
theorem twoComponentHomologyMap_mul (R : Type*) [CommRing R] (d : ℕ)
    (e f : Equiv.Perm (Fin (d + 1))) :
    twoComponentHomologyMap R d (e * f) =
      twoComponentHomologyMap R d e * twoComponentHomologyMap R d f := by
  unfold twoComponentHomologyMap
  rw [twoComponentPermutationMap_mul, ShortComplex.homologyMap_comp]
  rfl

/-- A group acting on the nodes and fixing the two components acts on actual graph homology. -/
def twoComponentHomologyRepresentation (R : Type*) [CommRing R] (d : ℕ)
    {G : Type*} [Group G] (α : G →* Equiv.Perm (Fin (d + 1))) :
    Representation R G (twoComponentComplex R d).homology where
  toFun g := twoComponentHomologyMap R d (α g)
  map_one' := by
    rw [map_one]
    exact twoComponentHomologyMap_eq_id R d 1 (fun _ => rfl)
  map_mul' g h := by rw [map_mul, twoComponentHomologyMap_mul]

/-- Fixing every node makes the genuine homology representation trivial. This is the
Galois-action input to splitness in the separate Raynaud–Picard theorem. -/
theorem twoComponentHomologyRepresentation_eq_trivial
    (R : Type*) [CommRing R] (d : ℕ)
    {G : Type*} [Group G] (α : G →* Equiv.Perm (Fin (d + 1)))
    (hα : ∀ g i, α g i = i) :
    twoComponentHomologyRepresentation R d α = Representation.trivial R G _ := by
  apply MonoidHom.ext
  intro g
  exact twoComponentHomologyMap_eq_id R d (α g) (hα g)

end Graph
