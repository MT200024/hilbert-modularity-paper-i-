/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.CharacterTwist
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.RingTheory.Polynomial.ScaleRoots

/-! # Common characteristic polynomials and character twists

Equality of representations at one coefficient embedding identifies their
common algebraic characteristic polynomials. The same polynomials then agree
at every coefficient embedding. We follow the coefficient comparison in
[TripathiGoswami, promotion of a fixed comparison].
-/

@[expose] public noncomputable section

namespace LinearMap

variable {K V : Type*} [Field K] [Infinite K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Multiplying an endomorphism by a nonzero scalar scales the roots of its
characteristic polynomial by that scalar. -/
theorem charpoly_smul_eq_scaleRoots (f : Module.End K V) (c : K) (hc : c ≠ 0) :
    (c • f).charpoly = f.charpoly.scaleRoots c := by
  apply Polynomial.funext
  intro x
  obtain ⟨y, rfl⟩ : ∃ y : K, c * y = x := ⟨x / c, by field_simp⟩
  rw [Polynomial.scaleRoots_eval_mul, charpoly_natDegree, eval_charpoly, eval_charpoly]
  have he : algebraMap K (Module.End K V) (c * y) - c • f =
      c • (algebraMap K (Module.End K V) y - f) := by
    simp only [Algebra.algebraMap_eq_smul_one, smul_sub, smul_smul]
  rw [he, det_smul]

end LinearMap

namespace Representation.Equiv

variable {K G V W : Type*} [Field K] [Monoid G]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  {ρ : Representation K G V} {σ : Representation K G W}

/-- Equivalent representations have the same characteristic polynomial at each element. -/
theorem charpoly_eq (e : ρ.Equiv σ) (g : G) : (ρ g).charpoly = (σ g).charpoly := by
  rw [← e.conj_apply_self g]
  exact (e.toLinearEquiv.charpoly_conj (ρ g)).symm

end Representation.Equiv

namespace Representation

variable {K G V : Type*} [Field K] [Infinite K] [Group G]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- A character twist scales the actual characteristic-polynomial roots. -/
theorem charpoly_characterTwist (ρ : Representation K G V) (χ : G →* Kˣ) (g : G) :
    (ρ.characterTwist χ g).charpoly = (ρ g).charpoly.scaleRoots (χ g : K) :=
  LinearMap.charpoly_smul_eq_scaleRoots (ρ g) (χ g) (χ g).ne_zero

/-- The same root-scaling formula holds for the tensor product with the character line. -/
theorem charpoly_characterTensor (ρ : Representation K G V) (χ : G →* Kˣ) (g : G) :
    (((ofCharacter χ).tprod ρ) g).charpoly = (ρ g).charpoly.scaleRoots (χ g : K) :=
  ((characterTwistTensorEquiv ρ χ).charpoly_eq g).trans (charpoly_characterTwist ρ χ g)

end Representation

namespace Representation

section CoefficientEmbedding

variable {E K G V W : Type*} [Field E] [Field K] [Infinite K] [Group G]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- The common polynomial of a character tensor is obtained by scaling by the
single algebraic character value before applying the coefficient embedding. -/
theorem charpoly_characterTensor_eq_map_scaleRoots
    (ι : E →+* K) (σ : Representation K G W) (χ : G →* Kˣ)
    (g : G) (Q : Polynomial E) (u : E)
    (hσ : (σ g).charpoly = Q.map ι) (hχ : (χ g : K) = ι u) :
    (((ofCharacter χ).tprod σ) g).charpoly = (Q.scaleRoots u).map ι := by
  have hQ : Q.Monic := Polynomial.monic_of_injective ι.injective
    (hσ ▸ (σ g).charpoly_monic)
  rw [charpoly_characterTensor, hσ, hχ, Polynomial.map_scaleRoots]
  simpa only [hQ.leadingCoeff, map_one] using (one_ne_zero : (1 : K) ≠ 0)

/-- An isomorphism at one coefficient embedding determines the underlying
algebraic polynomial, including the character twist. -/
theorem common_polynomial_eq_scaleRoots
    (ι : E →+* K) (ρ : Representation K G V) (σ : Representation K G W)
    (χ : G →* Kˣ) (e : ρ.Equiv ((ofCharacter χ).tprod σ))
    (g : G) (P Q : Polynomial E) (u : E)
    (hρ : (ρ g).charpoly = P.map ι) (hσ : (σ g).charpoly = Q.map ι)
    (hχ : (χ g : K) = ι u) : P = Q.scaleRoots u := by
  apply Polynomial.map_injective ι ι.injective
  rw [← hρ, e.charpoly_eq]
  exact charpoly_characterTensor_eq_map_scaleRoots ι σ χ g Q u hσ hχ

end CoefficientEmbedding

section Family

variable {E G J I : Type*} [Field E] [Group G]
  (L : J → Type*) [∀ j, Field (L j)] [∀ j, Infinite (L j)]
  (ι : ∀ j, E →+* L j)
  (V W : J → Type*) [∀ j, AddCommGroup (V j)] [∀ j, AddCommGroup (W j)]
  [∀ j, Module (L j) (V j)] [∀ j, Module (L j) (W j)]
  [∀ j, FiniteDimensional (L j) (V j)] [∀ j, FiniteDimensional (L j) (W j)]
  (ρ : ∀ j, Representation (L j) G (V j))
  (σ : ∀ j, Representation (L j) G (W j))
  (χ : G →* Eˣ) (t : I → G) (P Q : I → Polynomial E) (bad : J → Set I)

/-- A comparison at one coefficient place gives equality of actual twisted
characteristic polynomials at every other place, outside the union of their
exceptional sets. The one algebraic character is used at all places. -/
theorem charpoly_characterTensor_eq_of_compatible
    (hρ : ∀ j q, q ∉ bad j → (ρ j (t q)).charpoly = (P q).map (ι j))
    (hσ : ∀ j q, q ∉ bad j → (σ j (t q)).charpoly = (Q q).map (ι j))
    (j₀ : J)
    (e : (ρ j₀).Equiv ((ofCharacter ((Units.map (ι j₀).toMonoidHom).comp χ)).tprod (σ j₀)))
    (j : J) (q : I) (hq : q ∉ bad j ∪ bad j₀) :
    (ρ j (t q)).charpoly =
      (((ofCharacter ((Units.map (ι j).toMonoidHom).comp χ)).tprod (σ j)) (t q)).charpoly := by
  have hqj : q ∉ bad j := fun h => hq (Or.inl h)
  have hq₀ : q ∉ bad j₀ := fun h => hq (Or.inr h)
  have hP : P q = (Q q).scaleRoots (χ (t q) : E) :=
    common_polynomial_eq_scaleRoots (ι j₀) (ρ j₀) (σ j₀)
      ((Units.map (ι j₀).toMonoidHom).comp χ) e (t q) (P q) (Q q) (χ (t q))
      (hρ j₀ q hq₀) (hσ j₀ q hq₀) rfl
  rw [hρ j q hqj, hP]
  exact (charpoly_characterTensor_eq_map_scaleRoots (ι j) (σ j)
    ((Units.map (ι j).toMonoidHom).comp χ) (t q) (Q q) (χ (t q))
    (hσ j q hqj) rfl).symm

end Family

end Representation
