/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.Endomorphism
public import HilbertModularity.Geometry.TateModule.EndomorphismCompatibility
public import HilbertModularity.NumberTheory.AbsoluteFrobenius
public import HilbertModularity.NumberTheory.LocalSpecialization

/-! # Tate specialization at good reduction

The model is an actual abelian scheme over the local valuation ring. Its
generic and special fibres are scheme pullbacks. The named literature input
compares operators on their covariant Tate modules; it does not assume a
labelled characteristic polynomial or a manuscript compatibility conclusion.
-/

public section
noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj NumberField

namespace AlgebraicGeometry.GroupScheme

universe u

/-- The action of actual algebraic endomorphisms on the covariant Tate module
preserves products and powers. -/
def rationalTateEndomorphismMap (k : Type u) [Field k]
    (A : CommGrp (Over (Spec (CommRingCat.of k)))) (p : ℕ) [Fact p.Prime] :
    End A →+* Module.End ℚ_[p] (rationalTate k A.X p) :=
  (TateModule.rationalEndomorphismMap p (Points k (AlgebraicClosure k) A.X)).comp
    (pointsEndomorphismMap k (AlgebraicClosure k) A)

/-- Evaluation of the algebraic endomorphism action on geometric points. -/
theorem rationalTateEndomorphismMap_eq_rationalMap (k : Type u) [Field k]
    (A : CommGrp (Over (Spec (CommRingCat.of k)))) (p : ℕ) [Fact p.Prime]
    (f : End A) :
    rationalTateEndomorphismMap k A p f =
      TateModule.rationalMap p (pointsEndomorphismMap k (AlgebraicClosure k) A f) := by
  unfold rationalTateEndomorphismMap
  rw [RingHom.comp_apply, TateModule.rationalEndomorphismMap_apply]

@[simp]
theorem rationalTateEndomorphismMap_apply (k : Type u) [Field k]
    (A : CommGrp (Over (Spec (CommRingCat.of k)))) (p : ℕ) [Fact p.Prime]
    (f : End A) :
    rationalTateEndomorphismMap k A p f = rationalTateMap k (A := A.X) (B := A.X) p f.hom.hom.hom := by
  have h : pointsEndomorphismMap k (AlgebraicClosure k) A f =
      pointsMap k (AlgebraicClosure k) (A := A.X) (B := A.X) f.hom.hom.hom := by
    apply AddMonoidHom.ext
    intro x
    exact congrArg Additive.ofMul
      (CommGrp.pointsEndomorphismMap_apply (fieldPoint k (AlgebraicClosure k)) A f x)
  unfold rationalTateEndomorphismMap
  rw [RingHom.comp_apply, TateModule.rationalEndomorphismMap_apply, h]
  rfl

/-- The basis-free rational trace theorem for bundled algebraic endomorphisms. -/
theorem exists_rationalTateEndomorphismMap_trace (k : Type u) [Field k]
    (A : CommGrp (Over (Spec (CommRingCat.of k))))
    [IsProper A.X.hom] [Smooth A.X.hom] [GeometricallyConnected A.X.hom]
    (f : End A) (c : ℚ) :
    ∃ t : ℚ, ∀ (p : ℕ) (hp : p.Prime) (_ : (p : k) ≠ 0),
      letI : Fact p.Prime := ⟨hp⟩
      ∀ (_ : FiniteDimensional ℚ_[p] (rationalTate k A.X p)),
        LinearMap.trace ℚ_[p] _
          ((algebraMap ℚ ℚ_[p] c) • rationalTateEndomorphismMap k A p f) =
            algebraMap ℚ ℚ_[p] t := by
  simpa only [rationalTateEndomorphismMap_apply] using
    exists_rationalTateEndomorphism_trace k A.X f.hom.hom.hom c

variable (K : Type u) [Field K] [NumberField K]
  (P : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

/-- The generic point of the local valuation ring, using its inclusion in the
number field. -/
def localGenericPoint :
    Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of (P.valuationSubringAtPrime K)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (P.valuationSubringAtPrime K) K))

/-- The closed point, with residue field the original prime quotient. -/
def localSpecialPoint :
    Spec (CommRingCat.of (𝓞 K ⧸ P.asIdeal)) ⟶
      Spec (CommRingCat.of (P.valuationSubringAtPrime K)) :=
  Spec.map (CommRingCat.ofHom (P.localResidue (K := K)))

variable (B : CommGrp (Over (Spec (CommRingCat.of (P.valuationSubringAtPrime K)))))

attribute [local instance] Ideal.Quotient.field

/-- The actual generic fibre of the local model. -/
abbrev localGenericFiber : CommGrp (Over (Spec (CommRingCat.of K))) :=
  fiber K B (localGenericPoint K P)

/-- The actual reduction of the same local model. -/
abbrev localSpecialFiber : CommGrp (Over (Spec (CommRingCat.of (𝓞 K ⧸ P.asIdeal)))) :=
  fiber (𝓞 K ⧸ P.asIdeal) B (localSpecialPoint K P)

/-- Endomorphisms extend uniquely across good reduction.

[BLR, §1.2, Proposition 8] identifies an abelian scheme over a discrete
valuation ring with the Néron model of its generic fibre. Apply its mapping
property, as stated in [MilneAV, Chapter I, Theorem 17.1 and Remark 17.2, p. 70],
to this same smooth model. Uniqueness preserves the group operations.
Only the resulting bijection of actual endomorphisms is admitted. -/
theorem localGenericFiber_endomorphism_bijective
    [IsProper B.X.hom] [Smooth B.X.hom] [GeometricallyConnected B.X.hom] :
    Function.Bijective (fiberEndomorphismMap K B (localGenericPoint K P)) := by
  sorry

/-- Extend a generic-fibre coefficient action to the same good-reduction model.
The inverse of the endomorphism-ring isomorphism preserves all ring relations,
so extending generators separately is unnecessary. -/
def extendLocalGenericAction
    [IsProper B.X.hom] [Smooth B.X.hom] [GeometricallyConnected B.X.hom]
    {R : Type*} [CommRing R] (ψ : R →+* End (localGenericFiber K P B)) :
    R →+* End B :=
  (RingEquiv.ofBijective (fiberEndomorphismMap K B (localGenericPoint K P))
    (localGenericFiber_endomorphism_bijective K P B)).symm.toRingHom.comp ψ

/-- The extended action recovers exactly the supplied action on the generic fibre. -/
@[simp]
theorem fiberEndomorphismMap_extendLocalGenericAction
    [IsProper B.X.hom] [Smooth B.X.hom] [GeometricallyConnected B.X.hom]
    {R : Type*} [CommRing R] (ψ : R →+* End (localGenericFiber K P B)) (a : R) :
    fiberEndomorphismMap K B (localGenericPoint K P)
      (extendLocalGenericAction K P B ψ a) = ψ a := by
  exact (RingEquiv.ofBijective (fiberEndomorphismMap K B (localGenericPoint K P))
    (localGenericFiber_endomorphism_bijective K P B)).apply_symm_apply (ψ a)

/-- Specializing the extended action gives the original geometric-point action,
including its coefficient labels. -/
theorem fiberPointsAction_extendLocalGenericAction
    [IsProper B.X.hom] [Smooth B.X.hom] [GeometricallyConnected B.X.hom]
    {R : Type*} [CommRing R] (ψ : R →+* End (localGenericFiber K P B)) :
    fiberPointsAction K (AlgebraicClosure K) B (localGenericPoint K P) R
        (extendLocalGenericAction K P B ψ) =
      (pointsEndomorphismMap K (AlgebraicClosure K) (localGenericFiber K P B)).comp ψ := by
  ext a x
  simp only [fiberPointsAction_apply, fiberEndomorphismMap_extendLocalGenericAction,
    RingHom.comp_apply]

/-- Naturality of a Tate specialization with respect to the endomorphisms
of its single integral model. -/
def TateSpecializationNatural (p : ℕ) [Fact p.Prime]
    (e : rationalTate K (localGenericFiber K P B).X p ≃ₗ[ℚ_[p]]
      rationalTate (𝓞 K ⧸ P.asIdeal) (localSpecialFiber K P B).X p) : Prop :=
  (∀ f : End B,
            e.conj (rationalTateEndomorphismMap K (localGenericFiber K P B) p
                (fiberEndomorphismMap K B (localGenericPoint K P) f)) =
              rationalTateEndomorphismMap (𝓞 K ⧸ P.asIdeal) (localSpecialFiber K P B) p
                (fiberEndomorphismMap (𝓞 K ⧸ P.asIdeal) B (localSpecialPoint K P) f))

/-- Prime-to-residue-characteristic Tate specialization is natural for model
endomorphisms and takes arithmetic Galois Frobenius to algebraic Frobenius.

[MilneAV, Chapter IV, Theorem 3.5 and its proof, pp. 141–142; paragraph after
Corollary 3.6, p. 142], using the good-reduction model of Chapter I, §17.
The algebraic endomorphism is chosen on the special fibre before any auxiliary
prime or absolute Frobenius lift. The equivalence may depend on those choices.
Naturality is that of the prime-power torsion reduction maps in the proof.
Inertia acts trivially. The convention is covariant Tate modules and arithmetic
Frobenius; the cohomological dual at geometric Frobenius has the same polynomial.
There is no twist in this input and no assertion about labelled RM factors. -/
theorem exists_goodReductionTateSpecialization
    [IsProper B.X.hom] [Smooth B.X.hom] [GeometricallyConnected B.X.hom] :
    ∃ Fr : End (localSpecialFiber K P B),
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure K))) [Q.IsMaximal] [Q.LiesOver P.asIdeal]
        (p : ℕ) (hp : p.Prime) (_ : (p : 𝓞 K) ∉ P.asIdeal),
        letI : Fact p.Prime := ⟨hp⟩
        ∃ e : rationalTate K (localGenericFiber K P B).X p ≃ₗ[ℚ_[p]]
            rationalTate (𝓞 K ⧸ P.asIdeal) (localSpecialFiber K P B).X p,
          TateSpecializationNatural K P B p e ∧
          e.conj (tateRepresentation K (localGenericFiber K P B).X p
              (NumberField.arithmeticFrobenius K (AlgebraicClosure K) P.asIdeal Q)) =
            rationalTateEndomorphismMap (𝓞 K ⧸ P.asIdeal) (localSpecialFiber K P B) p Fr ∧
          (∀ g ∈ Q.inertia (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K),
            tateRepresentation K (localGenericFiber K P B).X p g = 1) := by
  sorry

/-- The common rational trace on the special fibre, before choosing an
auxiliary prime. -/
theorem exists_localSpecialFiber_endomorphism_trace
    [IsProper B.X.hom] [Smooth B.X.hom] [GeometricallyConnected B.X.hom]
    (f : End (localSpecialFiber K P B)) (c : ℚ) :
    ∃ t : ℚ, ∀ (p : ℕ) (hp : p.Prime) (_ : (p : 𝓞 K ⧸ P.asIdeal) ≠ 0),
      letI : Fact p.Prime := ⟨hp⟩
      ∀ (_ : FiniteDimensional ℚ_[p]
        (rationalTate (𝓞 K ⧸ P.asIdeal) (localSpecialFiber K P B).X p)),
        LinearMap.trace ℚ_[p] _ ((algebraMap ℚ ℚ_[p] c) •
          rationalTateEndomorphismMap (𝓞 K ⧸ P.asIdeal)
            (localSpecialFiber K P B) p f) = algebraMap ℚ ℚ_[p] t := by
  exact exists_rationalTateEndomorphismMap_trace (𝓞 K ⧸ P.asIdeal)
    (localSpecialFiber K P B) f c

/-- Conjugacy transports the weighted trace of a product with a power. -/
theorem trace_smul_mul_pow_of_conjugacy
    {F V W : Type*} [Field F] [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] [FiniteDimensional F V] [FiniteDimensional F W]
    (e : V ≃ₗ[F] W) (a b : Module.End F V) (a' b' : Module.End F W)
    (ha : e.conj a = a') (hb : e.conj b = b') (c : F) (n : ℕ) :
    LinearMap.trace F V (c • (a * b ^ n)) =
      LinearMap.trace F W (c • (a' * b' ^ n)) := by
  rw [← LinearMap.trace_conj' _ e, map_smul]
  change LinearMap.trace F W (c • e.conjRingEquiv (a * b ^ n)) = _
  rw [map_mul, map_pow]
  change LinearMap.trace F W (c • (e.conj a * (e.conj b) ^ n)) = _
  rw [ha, hb]

/-- Conjugate algebraic Tate operators have the trace of their special-fibre
composition. This abstract transport keeps the model pullbacks out of the
linear-algebra calculation. -/
theorem trace_weightedTateFrobenius_of_conjugacy
    {k k₀ : Type*} [Field k] [Field k₀]
    (A : CommGrp (Over (Spec (CommRingCat.of k))))
    (A₀ : CommGrp (Over (Spec (CommRingCat.of k₀))))
    (p : ℕ) [Fact p.Prime]
    [FiniteDimensional ℚ_[p] (rationalTate k A.X p)]
    [FiniteDimensional ℚ_[p] (rationalTate k₀ A₀.X p)]
    (e : rationalTate k A.X p ≃ₗ[ℚ_[p]] rationalTate k₀ A₀.X p)
    (f : End A) (f₀ Fr : End A₀)
    (g : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)
    (hf : e.conj (rationalTateEndomorphismMap k A p f) =
      rationalTateEndomorphismMap k₀ A₀ p f₀)
    (hg : e.conj (tateRepresentation k A.X p g) =
      rationalTateEndomorphismMap k₀ A₀ p Fr) (c : ℚ) (n : ℕ) :
    LinearMap.trace ℚ_[p] _ ((algebraMap ℚ ℚ_[p] c) •
      (rationalTateEndomorphismMap k A p f * tateRepresentation k A.X p g ^ n)) =
    LinearMap.trace ℚ_[p] _ ((algebraMap ℚ ℚ_[p] c) •
      rationalTateEndomorphismMap k₀ A₀ p (f₀ * Fr ^ n)) := by
  rw [map_mul, map_pow]
  exact trace_smul_mul_pow_of_conjugacy e _ _ _ _ hf hg _ n

/-- A natural Tate specialization transports the trace of each model
endomorphism composed with a Frobenius power. -/
theorem trace_model_frobenius_of_specialization
    (p : ℕ) [Fact p.Prime]
    [FiniteDimensional ℚ_[p] (rationalTate K (localGenericFiber K P B).X p)]
    (e : rationalTate K (localGenericFiber K P B).X p ≃ₗ[ℚ_[p]]
      rationalTate (𝓞 K ⧸ P.asIdeal) (localSpecialFiber K P B).X p)
    [FiniteDimensional ℚ_[p]
      (rationalTate (𝓞 K ⧸ P.asIdeal) (localSpecialFiber K P B).X p)]
    (he : TateSpecializationNatural K P B p e)
    (Fr : End (localSpecialFiber K P B))
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (hg : e.conj (tateRepresentation K (localGenericFiber K P B).X p g) =
      rationalTateEndomorphismMap (𝓞 K ⧸ P.asIdeal) (localSpecialFiber K P B) p Fr)
    (fB : End B) (c : ℚ) (n : ℕ) :
    LinearMap.trace ℚ_[p] _ ((algebraMap ℚ ℚ_[p] c) •
      (rationalTateEndomorphismMap K (localGenericFiber K P B) p
        (fiberEndomorphismMap K B (localGenericPoint K P) fB) *
        tateRepresentation K (localGenericFiber K P B).X p g ^ n)) =
    LinearMap.trace ℚ_[p] _ ((algebraMap ℚ ℚ_[p] c) •
      rationalTateEndomorphismMap (𝓞 K ⧸ P.asIdeal) (localSpecialFiber K P B) p
        (fiberEndomorphismMap (𝓞 K ⧸ P.asIdeal) B (localSpecialPoint K P) fB * Fr ^ n)) := by
  with_reducible
    refine trace_weightedTateFrobenius_of_conjugacy (k := K) (k₀ := 𝓞 K ⧸ P.asIdeal)
      (localGenericFiber K P B) (localSpecialFiber K P B) p e
      (fiberEndomorphismMap K B (localGenericPoint K P) fB)
      (fiberEndomorphismMap (𝓞 K ⧸ P.asIdeal) B (localSpecialPoint K P) fB)
      Fr g ?_ ?_ c n
  · unfold TateSpecializationNatural at he
    with_reducible exact he fB
  · with_reducible exact hg


/-- Every rational algebraic endomorphism of the generic fibre has a common
rational trace after composition with any fixed Frobenius power. The endomorphism
is first extended to the same good-reduction model; its reduction is composed
with the one algebraic Frobenius before the auxiliary prime is chosen.

This proves the full-space trace step of [TripathiGoswamiRevised,
Lemma `labelled-RM-compat`] from the two good-reduction inputs above and
[MilneAV, Chapter I, Proposition 10.20]. It does not assume a trace comparison. -/
theorem exists_goodReduction_model_weightedFrobeniusTrace
    [IsProper B.X.hom] [Smooth B.X.hom] [GeometricallyConnected B.X.hom]
    (fB : End B) (c : ℚ) (n : ℕ) :
    ∃ t : ℚ,
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure K))) [Q.IsMaximal] [Q.LiesOver P.asIdeal]
        (p : ℕ) (hp : p.Prime) (_ : (p : 𝓞 K) ∉ P.asIdeal),
        letI : Fact p.Prime := ⟨hp⟩
        ∀ (_ : FiniteDimensional ℚ_[p] (rationalTate K (localGenericFiber K P B).X p)),
          LinearMap.trace ℚ_[p] _ ((algebraMap ℚ ℚ_[p] c) •
            (rationalTateEndomorphismMap K (localGenericFiber K P B) p (fiberEndomorphismMap K B (localGenericPoint K P) fB) *
              tateRepresentation K (localGenericFiber K P B).X p
                (NumberField.arithmeticFrobenius K (AlgebraicClosure K) P.asIdeal Q) ^ n)) =
            algebraMap ℚ ℚ_[p] t := by
  obtain ⟨Fr, hFr⟩ := exists_goodReductionTateSpecialization K P B
  let fs : End (localSpecialFiber K P B) :=
    fiberEndomorphismMap (𝓞 K ⧸ P.asIdeal) B (localSpecialPoint K P) fB
  obtain ⟨t, ht⟩ := exists_localSpecialFiber_endomorphism_trace K P B (fs * Fr ^ n) c
  refine ⟨t, ?_⟩
  intro Q _ _ p hp hpP
  let : Fact p.Prime := ⟨hp⟩
  intro hfinite
  let := hfinite
  obtain ⟨e, he, heFr, _⟩ := hFr Q p hp hpP
  let : FiniteDimensional ℚ_[p]
      (rationalTate (𝓞 K ⧸ P.asIdeal) (localSpecialFiber K P B).X p) :=
    Module.Finite.of_surjective e.toLinearMap e.surjective
  have hchar : (p : 𝓞 K ⧸ P.asIdeal) ≠ 0 := by
    intro hz
    apply hpP
    exact (Ideal.Quotient.eq_zero_iff_mem).mp hz
  exact (trace_model_frobenius_of_specialization K P B p e he Fr _ heFr fB c n).trans
    (ht p hp hchar inferInstance)

/-- Extend an endomorphism to the good model, then apply the model trace theorem. -/
theorem exists_goodReduction_weightedFrobeniusTrace
    [IsProper B.X.hom] [Smooth B.X.hom] [GeometricallyConnected B.X.hom]
    (f : End (localGenericFiber K P B)) (c : ℚ) (n : ℕ) :
    ∃ t : ℚ,
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure K))) [Q.IsMaximal] [Q.LiesOver P.asIdeal]
        (p : ℕ) (hp : p.Prime) (_ : (p : 𝓞 K) ∉ P.asIdeal),
        letI : Fact p.Prime := ⟨hp⟩
        ∀ (_ : FiniteDimensional ℚ_[p] (rationalTate K (localGenericFiber K P B).X p)),
          LinearMap.trace ℚ_[p] _ ((algebraMap ℚ ℚ_[p] c) •
            (rationalTateEndomorphismMap K (localGenericFiber K P B) p f *
              tateRepresentation K (localGenericFiber K P B).X p
                (NumberField.arithmeticFrobenius K (AlgebraicClosure K) P.asIdeal Q) ^ n)) =
            algebraMap ℚ ℚ_[p] t := by
  obtain ⟨fB, rfl⟩ := (localGenericFiber_endomorphism_bijective K P B).surjective f
  exact exists_goodReduction_model_weightedFrobeniusTrace K P B fB c n

end AlgebraicGeometry.GroupScheme
