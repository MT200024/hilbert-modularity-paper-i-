/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.OrdinaryFlag
public import HilbertModularity.RepresentationTheory.LabelledHodgeTate
public import HilbertModularity.RepresentationTheory.WeightZeroQuotient

/-! # Labelled weights of an ordinary quotient character

The lower diagonal character in an adapted basis is the actual stable
rank-one quotient. Its local-labelled weights therefore agree with those
of that quotient. This gives the basis and weight part of the local
ordinarity argument in [TripathiGoswami].
-/

@[expose] public noncomputable section

namespace HodgeTate

variable (p : ℕ) [Fact p.Prime]
  {K E G V W : Type*} [Field K] [Field E] [Algebra ℚ_[p] K] [Algebra ℚ_[p] E]
  [FiniteDimensional ℚ_[p] K] [Algebra K ℂ_[p]] [IsScalarTower ℚ_[p] K ℂ_[p]]
  [Group G] (ι : G →* (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p))
  (hK : ∀ (g : G) (a : K), PadicComplex.galoisEquiv p (ι g)
    (algebraMap K ℂ_[p] a) = algebraMap K ℂ_[p] a)
  [AddCommGroup V] [Module E V] [Module ℚ_[p] V] [IsScalarTower ℚ_[p] E V]
  [AddCommGroup W] [Module E W] [Module ℚ_[p] W] [IsScalarTower ℚ_[p] E W]

/-- An actual coefficient-linear intertwiner preserves vanishing at all local labels. -/
theorem all_labelled_weights_zero_iff_of_equiv {ρ : Representation E G V}
    {ρ' : Representation E G W} (e : ρ.Equiv ρ') :
    (∀ τ, ∀ q : ℤ, q ≠ 0 → labelledWeightSpace p ι hK ρ q τ = ⊥) ↔
      ∀ τ, ∀ q : ℤ, q ≠ 0 → labelledWeightSpace p ι hK ρ' q τ = ⊥ := by
  rw [all_labelled_weights_zero_iff, all_labelled_weights_zero_iff]
  exact forall_congr' fun q => imp_congr_right fun _ =>
    weightSpace_eq_bot_iff (e.restrictScalars ℚ_[p]) q

/-- A rank-one quotient with all labelled weights zero yields an adapted triangular basis whose
lower diagonal character has that same genuine labelled period-space property. -/
theorem exists_upperTriangular_basis_with_labelled_weights_zero
    [FiniteDimensional E V] (ρ : Representation E G V)
    (S : Subrepresentation ρ) (hV : Module.finrank E V = 2)
    (hS : Module.finrank E (V ⧸ S.toSubmodule) = 1)
    (hweights : ∀ τ, ∀ q : ℤ, q ≠ 0 → labelledWeightSpace p ι hK
      (ρ.quotient S.toSubmodule S.apply_mem_toSubmodule) q τ = ⊥) :
    ∃ (b : Module.Basis (Fin 2) E V) (χ₁ χ₂ : G →* Eˣ) (a : G → E),
      b 0 ∈ S ∧
      Nonempty ((ρ.quotient S.toSubmodule S.apply_mem_toSubmodule).Equiv
        (Representation.ofCharacter χ₂)) ∧
      (∀ τ, ∀ q : ℤ, q ≠ 0 → labelledWeightSpace p ι hK
        (Representation.ofCharacter χ₂) q τ = ⊥) ∧
      ∀ g, LinearMap.toMatrix b b (ρ g) = !![(χ₁ g : E), a g; 0, (χ₂ g : E)] := by
  obtain ⟨b, χ₁, χ₂, a, hb, ⟨e⟩, hm⟩ := S.exists_basis_upperTriangular hV hS
  exact ⟨b, χ₁, χ₂, a, hb, ⟨e⟩,
    (all_labelled_weights_zero_iff_of_equiv p ι hK e).mp hweights, hm⟩

end HodgeTate

namespace HodgeTate

variable (p : ℕ) [Fact p.Prime]
  {K E G V : Type*} [Field K] [NontriviallyNormedField E] [CompleteSpace E]
  [Algebra ℚ_[p] K] [Algebra ℚ_[p] E] [FiniteDimensional ℚ_[p] K]
  [Algebra K ℂ_[p]] [IsScalarTower ℚ_[p] K ℂ_[p]]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (ι : G →* (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p))
  (hK : ∀ (g : G) (a : K), PadicComplex.galoisEquiv p (ι g)
    (algebraMap K ℂ_[p] a) = algebraMap K ℂ_[p] a)
  [AddCommGroup V] [Module E V] [TopologicalSpace V] [IsModuleTopology E V]
  [Module ℚ_[p] V] [IsScalarTower ℚ_[p] E V]
  [FiniteDimensional E V]

omit [CompleteSpace E] in
/-- A continuous rank-two representation with an actual labelled weight-zero quotient admits
continuous triangular characters with the required weights on its lower diagonal. -/
theorem exists_continuous_upperTriangular_basis_with_labelled_weights_zero
    (ρ : Representation E G V) (S : Subrepresentation ρ)
    (hV : Module.finrank E V = 2) (hS : Module.finrank E (V ⧸ S.toSubmodule) = 1)
    (hρ : ∀ v, Continuous (fun g => ρ g v))
    (hweights : ∀ τ, ∀ q : ℤ, q ≠ 0 → labelledWeightSpace p ι hK
      (ρ.quotient S.toSubmodule S.apply_mem_toSubmodule) q τ = ⊥) :
    ∃ (b : Module.Basis (Fin 2) E V) (χ₁ χ₂ : G →* Eˣ) (a : G → E),
      Continuous χ₁ ∧ Continuous χ₂ ∧ b 0 ∈ S ∧
      Nonempty ((ρ.quotient S.toSubmodule S.apply_mem_toSubmodule).Equiv
        (Representation.ofCharacter χ₂)) ∧
      (∀ τ, ∀ q : ℤ, q ≠ 0 → labelledWeightSpace p ι hK
        (Representation.ofCharacter χ₂) q τ = ⊥) ∧
      ∀ g, LinearMap.toMatrix b b (ρ g) = !![(χ₁ g : E), a g; 0, (χ₂ g : E)] := by
  obtain ⟨b, χ₁, χ₂, a, hc₁, hc₂, hb, ⟨e⟩, hm⟩ :=
    S.exists_continuous_characters_upperTriangular hV hS hρ
  exact ⟨b, χ₁, χ₂, a, hc₁, hc₂, hb, ⟨e⟩,
    (all_labelled_weights_zero_iff_of_equiv p ι hK e).mp hweights, hm⟩

omit [CompleteSpace E] in
/-- An actual ordinary quotient supplies continuous triangular characters, and the
fixed periods of its lower character span the full completed tensor. -/
theorem WeightZeroQuotient.exists_continuous_characters_upperTriangular
    {ρ : Representation E G V} (W : WeightZeroQuotient p ι hK ρ)
    (hV : Module.finrank E V = 2) (hρ : ∀ v, Continuous (fun g => ρ g v)) :
    ∃ (b : Module.Basis (Fin 2) E V) (χ₁ χ₂ : G →* Eˣ) (a : G → E),
      Continuous χ₁ ∧ Continuous χ₂ ∧ b 0 ∈ W.kernel ∧
      Nonempty ((ρ.quotient W.kernel.toSubmodule W.kernel.apply_mem_toSubmodule).Equiv
        (Representation.ofCharacter χ₂)) ∧
      (∀ τ, ∀ q : ℤ, q ≠ 0 → labelledWeightSpace p ι hK
        (Representation.ofCharacter χ₂) q τ = ⊥) ∧
      zeroWeightSpan (ι := ι) ((Representation.ofCharacter χ₂).restrictScalars ℚ_[p]) = ⊤ ∧
      ∀ g, LinearMap.toMatrix b b (ρ g) = !![(χ₁ g : E), a g; 0, (χ₂ g : E)] := by
  obtain ⟨b, χ₁, χ₂, a, hc₁, hc₂, hb, ⟨e⟩, hm⟩ :=
    W.kernel.exists_continuous_characters_upperTriangular hV W.finrank_eq_one hρ
  exact ⟨b, χ₁, χ₂, a, hc₁, hc₂, hb, ⟨e⟩,
    (all_labelled_weights_zero_iff_of_equiv p ι hK e).mp
      ((all_labelled_weights_zero_iff p ι hK _).mpr W.weights_zero),
    (zeroWeightSpan_eq_top_iff (ι := ι) (e.restrictScalars ℚ_[p])).mp
      W.zeroWeightSpan_eq_top, hm⟩

end HodgeTate
