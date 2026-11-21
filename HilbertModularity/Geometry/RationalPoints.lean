/- Assembled by AxiomProver. -/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.OpenImmersion

/-! # Rational points of schemes over a ring

A rational point is a section of the structural morphism. For affine schemes,
these sections are exactly algebra homomorphisms to the coefficient ring.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- A rational point of a scheme over `R` is a section over `Spec R`. -/
def Scheme.RationalPoint {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R) :=
  {s : Spec R ⟶ X // s ≫ f = 𝟙 (Spec R)}

namespace Scheme.RationalPoint

variable {R : CommRingCat.{u}} {X Y : Scheme.{u}}
  {f : X ⟶ Spec R} {g : Y ⟶ Spec R}

/-- Equal structural morphisms have identical rational points, with unchanged sections. -/
def congr {f g : X ⟶ Spec R} (h : f = g) :
    Scheme.RationalPoint f ≃ Scheme.RationalPoint g where
  toFun s := ⟨s.val, h ▸ s.property⟩
  invFun s := ⟨s.val, h.symm ▸ s.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Composition of a rational point with a morphism over the base. -/
def map (i : X ⟶ Y) (hi : i ≫ g = f) (s : Scheme.RationalPoint f) :
    Scheme.RationalPoint g :=
  ⟨s.val ≫ i, by rw [Category.assoc, hi, s.property]⟩

/-- A monomorphism is injective on rational points. -/
theorem map_injective (i : X ⟶ Y) [Mono i] (hi : i ≫ g = f) :
    Function.Injective (map i hi) := by
  intro s t h
  apply Subtype.ext
  exact (cancel_mono i).mp (congrArg Subtype.val h)

/-- A point whose image lies in an open chart lifts to a point of that chart. -/
def lift (i : X ⟶ Y) [IsOpenImmersion i] (hi : i ≫ g = f)
    (s : Scheme.RationalPoint g) (hs : Set.range s.val ⊆ Set.range i) :
    Scheme.RationalPoint f :=
  ⟨IsOpenImmersion.lift i s.val hs, by
    rw [← hi, ← Category.assoc, IsOpenImmersion.lift_fac, s.property]⟩

@[simp]
theorem map_lift (i : X ⟶ Y) [IsOpenImmersion i] (hi : i ≫ g = f)
    (s : Scheme.RationalPoint g) (hs : Set.range s.val ⊆ Set.range i) :
    map i hi (lift i hi s hs) = s := by
  apply Subtype.ext
  exact IsOpenImmersion.lift_fac i s.val hs

/-- For a field-valued point, membership of its unique image point suffices to lift. -/
theorem range_subset_of_mem {K : Type u} [Field K] {X Y : Scheme.{u}}
    (i : X ⟶ Y) (s : Spec (CommRingCat.of K) ⟶ Y)
    (hs : s (⊥ : PrimeSpectrum K) ∈ Set.range i) : Set.range s ⊆ Set.range i := by
  rintro _ ⟨x, rfl⟩
  simpa only [Subsingleton.elim x (⊥ : PrimeSpectrum K)] using hs

/-- Rational points split into one open chart and the complement inside a second chart. -/
def twoChartEquiv {K : Type u} [Field K] {U V X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) (i : U ⟶ X) (j : V ⟶ X)
    [IsOpenImmersion i] [IsOpenImmersion j]
    (hc : ∀ x, x ∈ Set.range i ∨ x ∈ Set.range j) :
    Scheme.RationalPoint f ≃
      Scheme.RationalPoint (i ≫ f) ⊕
        {s : Scheme.RationalPoint (j ≫ f) //
          j (s.val (⊥ : PrimeSpectrum K)) ∉ Set.range i} := by
  classical
  let F : Scheme.RationalPoint (i ≫ f) ⊕
      {s : Scheme.RationalPoint (j ≫ f) //
        j (s.val (⊥ : PrimeSpectrum K)) ∉ Set.range i} → Scheme.RationalPoint f :=
    Sum.elim (map i rfl) (fun s => map j rfl s.val)
  refine (Equiv.ofBijective F ⟨?_, ?_⟩).symm
  · intro a b hab
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (map_injective i rfl hab)
      | inr b =>
        exfalso
        apply b.property
        refine ⟨a.val (⊥ : PrimeSpectrum K), ?_⟩
        exact congrArg (fun s : Scheme.RationalPoint f => s.val (⊥ : PrimeSpectrum K)) hab
    | inr a =>
      cases b with
      | inl b =>
        exfalso
        apply a.property
        refine ⟨b.val (⊥ : PrimeSpectrum K), ?_⟩
        exact (congrArg (fun s : Scheme.RationalPoint f => s.val (⊥ : PrimeSpectrum K)) hab).symm
      | inr b =>
        exact congrArg Sum.inr (Subtype.ext (map_injective j rfl hab))
  · intro s
    by_cases hs : s.val (⊥ : PrimeSpectrum K) ∈ Set.range i
    · exact ⟨Sum.inl (lift i rfl s (range_subset_of_mem i s.val hs)), map_lift i rfl s _⟩
    · have hj : s.val (⊥ : PrimeSpectrum K) ∈ Set.range j := (hc _).resolve_left hs
      let t := lift j rfl s (range_subset_of_mem j s.val hj)
      have ht : j (t.val (⊥ : PrimeSpectrum K)) ∉ Set.range i := by
        have h := congrArg (fun q : Scheme.RationalPoint f => q.val (⊥ : PrimeSpectrum K))
          (map_lift j rfl s (range_subset_of_mem j s.val hj))
        exact h ▸ hs
      exact ⟨Sum.inr ⟨t, ht⟩, map_lift j rfl s _⟩

end Scheme.RationalPoint

set_option backward.isDefEq.respectTransparency false in
/-- Rational points of an affine scheme are algebra maps to its base ring. -/
def Scheme.affineRationalPointEquiv (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :
    Scheme.RationalPoint (Spec.map (CommRingCat.ofHom (algebraMap R A))) ≃ (A →ₐ[R] R) where
  toFun s := ⟨(Spec.preimage s.val).hom, by
    intro r
    have h : CommRingCat.ofHom (algebraMap R A) ≫ Spec.preimage s.val = 𝟙 _ := by
      apply Spec.map_injective
      simpa using s.property
    exact congr($h r)⟩
  invFun φ := ⟨Spec.map (CommRingCat.ofHom φ.toRingHom), by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext r
    exact φ.commutes r⟩
  left_inv s := by apply Subtype.ext; simp
  right_inv φ := by apply AlgHom.coe_ringHom_injective; simp

end AlgebraicGeometry
