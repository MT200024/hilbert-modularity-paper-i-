/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.DeterminantCharacter
public import HilbertModularity.RepresentationTheory.ResidualDeterminant
public import HilbertModularity.NumberTheory.ResidualRigidity
public import HilbertModularity.NumberTheory.LocalSpecialization.FiniteSupport

/-! # Determinant rigidity for representations over coefficient completions

Common algebraic determinant values are determined by residual congruences in
infinitely many residue characteristics. The congruences here come from actual
full stable lattices in representations over the corresponding adic completions.
This implements the lattice-to-arithmetic step of
[TripathiGoswami, determinant rigidity]. Existence of the compatible system
and arithmetic Frobenius density are separate geometric inputs.
-/

@[expose] public noncomputable section

namespace IsDedekindDomain.HeightOneSpectrum

variable {R K G J : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K] [Monoid G]
  (P : J → HeightOneSpectrum R) (V : J → Type*)
  [∀ j, AddCommGroup (V j)] [∀ j, Module ((P j).adicCompletion K) (V j)]
  [∀ j, Module ((P j).adicCompletionIntegers K) (V j)]
  [∀ j, IsScalarTower ((P j).adicCompletionIntegers K) ((P j).adicCompletion K) (V j)]
  (ρ : ∀ j, Representation ((P j).adicCompletion K) G (V j))
  (L : ∀ j, Subrepresentation ((ρ j).restrictScalars ((P j).adicCompletionIntegers K)))
  [∀ j, Submodule.IsLattice ((P j).adicCompletion K) (L j).toSubmodule]
  {ι : J → Type*}
  (b : ∀ j, Module.Basis (ι j) ((P j).adicCompletionIntegers K) (L j).toSubmodule)

include b in
/-- A common algebraic determinant equals its expected value when actual lattice
reductions agree in infinitely many distinct residue characteristics. -/
theorem eq_of_infinite_completion_determinant_congruences
    (hP : (Set.range fun j => ringChar (R ⧸ (P j).asIdeal)).Infinite)
    (g : G) (x y : K) (hy : y ≠ 0)
    (hx : ∀ j, LinearMap.det (ρ j g) = algebraMap K ((P j).adicCompletion K) x)
    (hunit : ∀ j, (P j).valuation K y = 1)
    (hres : ∀ j, LinearMap.det (((L j).toRepresentation.baseChange
        (IsLocalRing.ResidueField ((P j).adicCompletionIntegers K))) g) =
      (P j).completionResidueMap ((P j).specialization y (hunit j).le)) : x = y := by
  have hratio : x / y = 1 := eq_one_of_infinite_residue_characteristics (x / y)
    (Set.range fun j => ringChar (R ⧸ (P j).asIdeal)) hP (by
      intro ell hell
      obtain ⟨j, rfl⟩ := hell
      exact ⟨P j, rfl, (P j).completion_determinant_ratio_specialization
        (ρ j) (L j) (b j) g x y (hx j) (hunit j) (hres j)⟩)
  exact (div_eq_one_iff_eq hy).mp hratio

end IsDedekindDomain.HeightOneSpectrum

namespace ContinuousMonoidHom

open IsDedekindDomain

/-- A continuous determinant-ratio character is trivial when its algebraic
values on a dense family satisfy actual completed lattice congruences in
infinitely many residue characteristics. The good primes may depend on the
dense-family element. -/
theorem eq_one_of_infinite_completed_lattice_congruences
    {R K F G I J : Type*} [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field F] [TopologicalSpace F] [T2Space F] [Algebra K F]
    [Monoid G] [TopologicalSpace G]
    (P : J → HeightOneSpectrum R) (V : J → Type*)
    [∀ j, AddCommGroup (V j)] [∀ j, Module ((P j).adicCompletion K) (V j)]
    [∀ j, Module ((P j).adicCompletionIntegers K) (V j)]
    [∀ j, IsScalarTower ((P j).adicCompletionIntegers K) ((P j).adicCompletion K) (V j)]
    (ρ : ∀ j, Representation ((P j).adicCompletion K) G (V j))
    (L : ∀ j, Subrepresentation ((ρ j).restrictScalars ((P j).adicCompletionIntegers K)))
    [∀ j, Submodule.IsLattice ((P j).adicCompletion K) (L j).toSubmodule]
    {ι : J → Type*}
    (b : ∀ j, Module.Basis (ι j) ((P j).adicCompletionIntegers K) (L j).toSubmodule)
    (χ : G →ₜ* Fˣ) (t : I → G) (ht : DenseRange t) (x y : I → K)
    (hχ : ∀ i, (χ (t i) : F) = algebraMap K F (x i / y i))
    (S : I → Set J)
    (hS : ∀ i, ((fun j => ringChar (R ⧸ (P j).asIdeal)) '' S i).Infinite)
    (hx : ∀ i j, j ∈ S i →
      LinearMap.det (ρ j (t i)) = algebraMap K ((P j).adicCompletion K) (x i))
    (hunit : ∀ i j, j ∈ S i → (P j).valuation K (y i) = 1)
    (hres : ∀ i j (hj : j ∈ S i), LinearMap.det (((L j).toRepresentation.baseChange
        (IsLocalRing.ResidueField ((P j).adicCompletionIntegers K))) (t i)) =
      (P j).completionResidueMap ((P j).specialization (y i) (hunit i j hj).le)) :
    χ = 1 := by
  apply eq_one_of_infinite_residual_congruences (R := R) χ t ht (fun i => x i / y i) hχ
    (fun i => (fun j => ringChar (R ⧸ (P j).asIdeal)) '' S i) hS
  intro i ell hell
  obtain ⟨j, hj, rfl⟩ := hell
  exact ⟨P j, rfl, (P j).completion_determinant_ratio_specialization
    (ρ j) (L j) (b j) (t i) (x i) (y i) (hx i j hj) (hunit i j hj) (hres i j hj)⟩

end ContinuousMonoidHom

namespace Representation

open IsDedekindDomain

/-- The actual continuous determinant character equals the expected character
when compatible algebraic Frobenius values have matching completed lattice
reductions in infinitely many residue characteristics. Density is an explicit
input; no arithmetic density theorem is asserted here. -/
theorem continuousDeterminantCharacter_eq_of_completed_lattice_congruences
    {R K F G I J W κ : Type*} [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field F] [TopologicalSpace F] [IsTopologicalRing F] [T2Space F] [Algebra K F]
    [Group G] [TopologicalSpace G] [ContinuousInv G]
    [AddCommGroup W] [Module F W] [TopologicalSpace W]
    [Fintype κ] [DecidableEq κ] (c : Module.Basis κ F W)
    (hc : ∀ k, Continuous (c.coord k))
    (τ : Representation F G W) (hτ : ∀ w, Continuous (fun g => τ g w))
    (μ : G →ₜ* Fˣ)
    (P : J → HeightOneSpectrum R) (V : J → Type*)
    [∀ j, AddCommGroup (V j)] [∀ j, Module ((P j).adicCompletion K) (V j)]
    [∀ j, Module ((P j).adicCompletionIntegers K) (V j)]
    [∀ j, IsScalarTower ((P j).adicCompletionIntegers K) ((P j).adicCompletion K) (V j)]
    (ρ : ∀ j, Representation ((P j).adicCompletion K) G (V j))
    (L : ∀ j, Subrepresentation ((ρ j).restrictScalars ((P j).adicCompletionIntegers K)))
    [∀ j, Submodule.IsLattice ((P j).adicCompletion K) (L j).toSubmodule]
    {ι : J → Type*}
    (b : ∀ j, Module.Basis (ι j) ((P j).adicCompletionIntegers K) (L j).toSubmodule)
    (t : I → G) (ht : DenseRange t) (x y : I → K)
    (hτx : ∀ i, LinearMap.det (τ (t i)) = algebraMap K F (x i))
    (hμy : ∀ i, (μ (t i) : F) = algebraMap K F (y i))
    (S : I → Set J)
    (hS : ∀ i, ((fun j => ringChar (R ⧸ (P j).asIdeal)) '' S i).Infinite)
    (hx : ∀ i j, j ∈ S i →
      LinearMap.det (ρ j (t i)) = algebraMap K ((P j).adicCompletion K) (x i))
    (hunit : ∀ i j, j ∈ S i → (P j).valuation K (y i) = 1)
    (hres : ∀ i j (hj : j ∈ S i), LinearMap.det (((L j).toRepresentation.baseChange
        (IsLocalRing.ResidueField ((P j).adicCompletionIntegers K))) (t i)) =
      (P j).completionResidueMap ((P j).specialization (y i) (hunit i j hj).le)) :
    continuousDeterminantCharacter c hc τ hτ = μ := by
  apply div_eq_one.mp
  apply ContinuousMonoidHom.eq_one_of_infinite_completed_lattice_congruences
    P V ρ L b (continuousDeterminantCharacter c hc τ hτ / μ) t ht x y
      ?_ S hS hx hunit hres
  intro i
  change ((continuousDeterminantCharacter c hc τ hτ (t i) / μ (t i) : Fˣ) : F) = _
  rw [Units.val_div_eq_div_val, continuousDeterminantCharacter_coe]
  rw [hτx, hμy, map_div₀]

/-- Finite exclusions of nonunit algebraic values preserve the determinant-rigidity
conclusion. The residual congruence is needed only where the expected value is
a local unit; this holds at all but finitely many coefficient primes. -/
theorem continuousDeterminantCharacter_eq_of_infinite_residual_congruences
    {R K F G I J W κ : Type*} [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field F] [TopologicalSpace F] [IsTopologicalRing F] [T2Space F] [Algebra K F]
    [Group G] [TopologicalSpace G] [ContinuousInv G]
    [AddCommGroup W] [Module F W] [TopologicalSpace W]
    [Fintype κ] [DecidableEq κ] (c : Module.Basis κ F W)
    (hc : ∀ k, Continuous (c.coord k))
    (τ : Representation F G W) (hτ : ∀ w, Continuous (fun g => τ g w))
    (μ : G →ₜ* Fˣ)
    (P : J → HeightOneSpectrum R) (V : J → Type*)
    [∀ j, AddCommGroup (V j)] [∀ j, Module ((P j).adicCompletion K) (V j)]
    [∀ j, Module ((P j).adicCompletionIntegers K) (V j)]
    [∀ j, IsScalarTower ((P j).adicCompletionIntegers K) ((P j).adicCompletion K) (V j)]
    (ρ : ∀ j, Representation ((P j).adicCompletion K) G (V j))
    (L : ∀ j, Subrepresentation ((ρ j).restrictScalars ((P j).adicCompletionIntegers K)))
    [∀ j, Submodule.IsLattice ((P j).adicCompletion K) (L j).toSubmodule]
    {ι : J → Type*}
    (b : ∀ j, Module.Basis (ι j) ((P j).adicCompletionIntegers K) (L j).toSubmodule)
    (t : I → G) (ht : DenseRange t) (x y : I → K)
    (hτx : ∀ i, LinearMap.det (τ (t i)) = algebraMap K F (x i))
    (hμy : ∀ i, (μ (t i) : F) = algebraMap K F (y i))
    (S : I → Set J)
    (hS : ∀ i, ((fun j => ringChar (R ⧸ (P j).asIdeal)) '' S i).Infinite)
    (hx : ∀ i j, j ∈ S i →
      LinearMap.det (ρ j (t i)) = algebraMap K ((P j).adicCompletion K) (x i))
    (hres : ∀ i j, j ∈ S i → ∀ hu : (P j).valuation K (y i) = 1, LinearMap.det (((L j).toRepresentation.baseChange
        (IsLocalRing.ResidueField ((P j).adicCompletionIntegers K))) (t i)) =
      (P j).completionResidueMap ((P j).specialization (y i) hu.le)) :
    continuousDeterminantCharacter c hc τ hτ = μ := by
  have hy (i : I) : y i ≠ 0 := fun h => (μ (t i)).ne_zero (by rw [hμy, h, map_zero])
  exact continuousDeterminantCharacter_eq_of_completed_lattice_congruences
    c hc τ hτ μ P V ρ L b t ht x y hτx hμy
    (fun i => {j ∈ S i | (P j).valuation K (y i) = 1})
    (fun i => HeightOneSpectrum.infinite_residue_characteristics_of_unit
      P (S i) (hS i) (y i) (hy i))
    (fun i j hj => hx i j hj.1) (fun _ _ hj => hj.2)
    (fun i j hj => hres i j hj.1 hj.2)

end Representation
