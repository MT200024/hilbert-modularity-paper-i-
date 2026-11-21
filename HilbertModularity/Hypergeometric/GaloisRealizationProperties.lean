/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.GaloisRealization

/-! # Character projectors and Euler-curve localization

For a tame Euler curve, the boundary of its branch-open affine part consists
of deck-fixed points.  The following linear-algebra result is the deduction
that makes its nontrivial primitive character component insensitive to that
boundary.  Applying it to geometric cohomology still requires the actual
localization maps and their compatibility with the chosen cohomology theory;
the torsion localization sequence is [src_milne_lec, Theorem 16.1 and
Corollary 16.2], while the rational pro-étale comparison is a separate input.
-/

public noncomputable section

namespace Representation

variable {L G V W B : Type*} [Field L] [CommGroup G] [Fintype G]
  [AddCommGroup V] [Module L V] [AddCommGroup W] [Module L W]
  [AddCommGroup B] [Module L B]

/-- An equivariant linear map commutes with the same character average on
its source and target. -/
theorem characterProjector_map (χ : G →* Lˣ)
    (ρV : Representation L G V) (ρW : Representation L G W)
    (j : V →ₗ[L] W)
    (hj : ∀ g : G, (ρW g).comp j = j.comp (ρV g)) (v : V) :
    j (characterProjector χ ρV v) = characterProjector χ ρW (j v) := by
  classical
  simp only [characterProjector, LinearMap.smul_apply, LinearMap.sum_apply]
  rw [map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro g _
  rw [map_smul]
  congr 1
  exact congrArg (fun f : V →ₗ[L] W => f v) (hj g).symm

/-- The boundary map kills a nontrivial character component whenever the
deck group acts trivially on the boundary. -/
theorem characterProjector_boundary_zero (χ : G →* Lˣ)
    (ρW : Representation L G W) (ρB : Representation L G B)
    (b : W →ₗ[L] B)
    (hb : ∀ g : G, (ρB g).comp b = b.comp (ρW g))
    (htrivial : ∀ (g : G) (z : B), ρB g z = z)
    (hχ : ∃ g : G, (χ g : L) ≠ 1) (w : W) :
    b (characterProjector χ ρW w) = 0 := by
  obtain ⟨g, hg⟩ := hχ
  let y := b (characterProjector χ ρW w)
  have hy : y = (χ g : L) • y := by
    calc
      y = ρB g y := (htrivial g y).symm
      _ = b (ρW g (characterProjector χ ρW w)) :=
        congrArg (fun f : W →ₗ[L] B => f (characterProjector χ ρW w)) (hb g)
      _ = (χ g : L) • y := by
        rw [characterProjector_eigen, map_smul]
  have hz : ((χ g : L) - 1) • y = 0 := by
    rw [sub_smul, one_smul, sub_eq_zero]
    exact hy.symm
  exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hg)

/-- Exact equivariant localization identifies the nontrivial projector
images when the deck action on the boundary is trivial. -/
def characterProjectorLocalizationEquiv (χ : G →* Lˣ)
    (ρV : Representation L G V) (ρW : Representation L G W)
    (ρB : Representation L G B) (j : V →ₗ[L] W) (b : W →ₗ[L] B)
    (hj : ∀ g : G, (ρW g).comp j = j.comp (ρV g))
    (hb : ∀ g : G, (ρB g).comp b = b.comp (ρW g))
    (htrivial : ∀ (g : G) (z : B), ρB g z = z)
    (hχ : ∃ g : G, (χ g : L) ≠ 1)
    (hcard : (Fintype.card G : L) ≠ 0)
    (hinj : Function.Injective j) (hexact : b.ker = j.range) :
    (characterProjector χ ρV).range ≃ₗ[L]
      (characterProjector χ ρW).range := by
  let f : (characterProjector χ ρV).range →ₗ[L]
      (characterProjector χ ρW).range :=
    { toFun := fun v => ⟨j v, by
        obtain ⟨u, hu⟩ := v.property
        refine ⟨j u, ?_⟩
        rw [← characterProjector_map χ ρV ρW j hj u, hu]⟩
      map_add' := by
        intro v w
        apply Subtype.ext
        change j ((v : V) + w) = j v + j w
        exact map_add j (v : V) (w : V)
      map_smul' := by
        intro a v
        apply Subtype.ext
        change j (a • (v : V)) = a • j v
        exact map_smul j a (v : V) }
  refine LinearEquiv.ofBijective f ⟨?_, ?_⟩
  · intro v w hvw
    apply Subtype.ext
    apply hinj
    exact congrArg Subtype.val hvw
  · rintro ⟨w, hw⟩
    obtain ⟨u, rfl⟩ := hw
    have hzero : b (characterProjector χ ρW u) = 0 :=
      characterProjector_boundary_zero χ ρW ρB b hb htrivial hχ u
    have hmem : characterProjector χ ρW u ∈ j.range := by
      rw [← hexact]
      exact LinearMap.mem_ker.mpr hzero
    obtain ⟨v, hv⟩ := hmem
    refine ⟨⟨characterProjector χ ρV v, ⟨v, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    change j (characterProjector χ ρV v) = characterProjector χ ρW u
    rw [characterProjector_map χ ρV ρW j hj v, hv]
    exact congrArg (fun f : W →ₗ[L] W => f u)
      (characterProjector_idempotent χ ρW hcard)

/-- The localization equivalence is induced by the actual restriction map. -/
theorem characterProjectorLocalizationEquiv_apply (χ : G →* Lˣ)
    (ρV : Representation L G V) (ρW : Representation L G W)
    (ρB : Representation L G B) (j : V →ₗ[L] W) (b : W →ₗ[L] B)
    (hj : ∀ g : G, (ρW g).comp j = j.comp (ρV g))
    (hb : ∀ g : G, (ρB g).comp b = b.comp (ρW g))
    (htrivial : ∀ (g : G) (z : B), ρB g z = z)
    (hχ : ∃ g : G, (χ g : L) ≠ 1)
    (hcard : (Fintype.card G : L) ≠ 0)
    (hinj : Function.Injective j) (hexact : b.ker = j.range)
    (v : (characterProjector χ ρV).range) :
    ((characterProjectorLocalizationEquiv χ ρV ρW ρB j b hj hb htrivial hχ hcard
      hinj hexact v : (characterProjector χ ρW).range) : W) = j v := by
  unfold characterProjectorLocalizationEquiv
  rfl

/-- Equivariant endomorphisms on the two cohomology spaces induce the same
endomorphism on their identified nontrivial character components. -/
theorem characterProjectorLocalizationEquiv_naturality (χ : G →* Lˣ)
    (ρV : Representation L G V) (ρW : Representation L G W)
    (ρB : Representation L G B) (j : V →ₗ[L] W) (b : W →ₗ[L] B)
    (hj : ∀ g : G, (ρW g).comp j = j.comp (ρV g))
    (hb : ∀ g : G, (ρB g).comp b = b.comp (ρW g))
    (htrivial : ∀ (g : G) (z : B), ρB g z = z)
    (hχ : ∃ g : G, (χ g : L) ≠ 1)
    (hcard : (Fintype.card G : L) ≠ 0)
    (hinj : Function.Injective j) (hexact : b.ker = j.range)
    (αV : V →ₗ[L] V) (αW : W →ₗ[L] W)
    (hαV : ∀ v ∈ (characterProjector χ ρV).range,
      αV v ∈ (characterProjector χ ρV).range)
    (hαW : ∀ w ∈ (characterProjector χ ρW).range,
      αW w ∈ (characterProjector χ ρW).range)
    (hα : αW.comp j = j.comp αV)
    (v : (characterProjector χ ρV).range) :
    characterProjectorLocalizationEquiv χ ρV ρW ρB j b hj hb htrivial hχ hcard
        hinj hexact ⟨αV v, hαV v v.property⟩ =
      ⟨αW (characterProjectorLocalizationEquiv χ ρV ρW ρB j b hj hb htrivial
        hχ hcard hinj hexact v),
        hαW _ (characterProjectorLocalizationEquiv χ ρV ρW ρB j b hj hb
          htrivial hχ hcard hinj hexact v).property⟩ := by
  apply Subtype.ext
  change j (αV v) = αW (j v)
  exact congrArg (fun f : V →ₗ[L] W => f v) hα.symm

/-- A deck-equivariant endomorphism preserves the selected character component. -/
theorem characterProjector_endomorphism_mem_range (χ : G →* Lˣ)
    (ρ : Representation L G V) (α : V →ₗ[L] V)
    (hα : ∀ g : G, (ρ g).comp α = α.comp (ρ g))
    (v : V) (hv : v ∈ (characterProjector χ ρ).range) :
    α v ∈ (characterProjector χ ρ).range := by
  obtain ⟨u, rfl⟩ := hv
  refine ⟨α u, ?_⟩
  exact congrArg (fun f : V →ₗ[L] V => f u)
    (characterProjector_comm χ ρ α hα)

end Representation
