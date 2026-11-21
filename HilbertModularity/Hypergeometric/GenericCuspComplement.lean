/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.ProjectiveLine.GenericFiberPath
public import HilbertModularity.Geometry.Etale.PointedPullbackMonodromy
public import HilbertModularity.Hypergeometric.RMComparison
public import HilbertModularity.Monodromy.CuspTriple

/-! # Geometric complement from the actual oriented local classes

The three prescribed local matrices and their product give the intertwiner
with the actual complement pullback. The cusp data are explicit hypotheses;
no new literature input is introduced in this deduction.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace HilbertModularity.Hypergeometric

private theorem toMatrix_map_representationEquiv
    {L G V W : Type*} [Field L] [Group G]
    [AddCommGroup V] [Module L V] [AddCommGroup W] [Module L W]
    {ρ : Representation L G V} {σ : Representation L G W}
    (e : ρ.Equiv σ) (c : Module.Basis (Fin 2) L V) (g : G) :
    LinearMap.toMatrix (c.map e.toLinearEquiv) (c.map e.toLinearEquiv) (σ g) =
      LinearMap.toMatrix c c (ρ g) := by
  rw [LinearMap.toMatrix_map_left, LinearMap.toMatrix_map_right]
  congr 1
  apply LinearMap.ext
  intro v
  change e.symm (σ g (e v)) = ρ g v
  have he := congrArg (fun f : V →ₗ[L] W => f v) (e.isIntertwining' g)
  change e (ρ g v) = σ g (e v) at he
  rw [← he]
  exact e.toLinearEquiv.symm_apply_apply _

private theorem toMatrix_map_representationEquiv_at
    {L G H V W : Type*} [Field L] [Group G] [Group H]
    [AddCommGroup V] [Module L V] [AddCommGroup W] [Module L W]
    (ρ : Representation L H V) (σ : Representation L G W) (φ : H →* G)
    (e : ρ.Equiv (σ.comp φ)) (c : Module.Basis (Fin 2) L V)
    (g : H) (u : G) (hu : φ g = u) :
    LinearMap.toMatrix (c.map e.toLinearEquiv) (c.map e.toLinearEquiv) (σ u) =
      LinearMap.toMatrix c c (ρ g) :=
  (congrArg (fun t => LinearMap.toMatrix (c.map e.toLinearEquiv)
    (c.map e.toLinearEquiv) (σ t)) hu).symm.trans
      (toMatrix_map_representationEquiv e c g)

private theorem localClasses_transport
    {L G H V W : Type*} [Field L] [Group G] [Group H]
    [AddCommGroup V] [Module L V] [AddCommGroup W] [Module L W]
    (ρ : Representation L H V) (σ : Representation L G W) (φ : H →* G)
    (e : ρ.Equiv (σ.comp φ)) (g : Fin 3 → H) (u : Fin 3 → G)
    (hu : ∀ i, φ (g i) = u i) (M : Fin 3 → Matrix (Fin 2) (Fin 2) L)
    (hM : ∀ i, ∃ c : Module.Basis (Fin 2) L V,
      LinearMap.toMatrix c c (ρ (g i)) = M i) :
    ∀ i, ∃ c : Module.Basis (Fin 2) L W,
      LinearMap.toMatrix c c (σ (u i)) = M i := by
  intro i
  obtain ⟨c, hc⟩ := hM i
  exact ⟨c.map e.toLinearEquiv,
    (toMatrix_map_representationEquiv_at ρ σ φ e c (g i) (u i) (hu i)).trans hc⟩

/-- The actual midpoint cusp matrices give both complement invariance and
absolute irreducibility. This isolates the representation-theoretic deduction
from the generic-point inertia transport. -/
private theorem complementEquiv_of_cusp_matrices
    (K L : Type) [Field K] [CharZero K]
    [NontriviallyNormedField L] [CompleteSpace L]
    (F : Scheme.EtaleLocalSystem K (ProjectiveLine.punctured K) L) :
    let x := ProjectiveLine.puncturedPoint K (ProjectiveLine.midpointParameter K)
    let π := Scheme.etaleFundamentalGroupMap (ProjectiveLine.puncturedToSpec K) K x
    let ρ := Scheme.fiberMonodromy K (ProjectiveLine.punctured K) F.algebraicFunctor x
    ∀ (a b d : π.ker), a * b * d = 1 →
      Dense (Subgroup.closure ({a, b} : Set π.ker) : Set π.ker) →
      ∀ (α : π.ker ≃ₜ* π.ker),
        (∀ g : π.ker, (α g : Scheme.etaleFundamentalGroup K x) =
          ProjectiveLine.complementFundamentalAutomorphism K g) →
        α a = b → α b = a → ∀ (τ : L), τ ≠ 2 →
        ∀ (b₀ b₁ b₂ : Module.Basis (Fin 2) L
          (F.toFunctor.obj (Scheme.etaleFiberPoint K (ProjectiveLine.punctured K) x))),
          LinearMap.toMatrix b₀ b₀ (ρ a) = Monodromy.U0 →
          LinearMap.toMatrix b₁ b₁ (ρ b) = Monodromy.U1 τ →
          LinearMap.toMatrix b₂ b₂ (ρ d) = Monodromy.Uinf τ →
          Nonempty (Representation.Equiv (ρ.comp π.ker.subtype)
            ((Scheme.fiberMonodromy K (ProjectiveLine.punctured K)
              (F.complementPullback K L).algebraicFunctor x).comp π.ker.subtype)) ∧
          (Representation.baseChange (AlgebraicClosure L) (ρ.comp π.ker.subtype)).IsIrreducible := by
  dsimp only
  intro a b d hprod hdense α hα ha hb τ hτ b₀ b₁ b₂ h0 h1 h2
  let x := ProjectiveLine.puncturedPoint K (ProjectiveLine.midpointParameter K)
  let π := Scheme.etaleFundamentalGroupMap (ProjectiveLine.puncturedToSpec K) K x
  let V := F.toFunctor.obj (Scheme.etaleFiberPoint K (ProjectiveLine.punctured K) x)
  let ρ : Representation L (Scheme.etaleFundamentalGroup K x) V :=
    Scheme.fiberMonodromy K (ProjectiveLine.punctured K) F.algebraicFunctor x
  have hcont : ∀ v, Continuous (fun g : π.ker => b₀.equivFun (ρ g v)) := by
    intro v
    let bc : V →ₗ[L] (Fin 2 → L) := b₀.equivFun.toLinearMap
    have hbc : Continuous bc := bc.continuous_of_finiteDimensional
    exact hbc.comp ((F.continuous_monodromy x v).comp continuous_subtype_val)
  obtain ⟨⟨H⟩, hAbs⟩ := Monodromy.nonempty_equiv_comp_of_standard_cusp_triple
    (ρ.comp π.ker.subtype) a b d hprod hdense α.toMulEquiv α.continuous ha hb
    τ hτ b₀ b₁ b₂ h0 h1 h2 hcont
  have hcomp : (ρ.comp π.ker.subtype).comp α.toMonoidHom =
      (ρ.comp (ProjectiveLine.complementFundamentalAutomorphism K).toMonoidHom).comp
        π.ker.subtype := by
    apply MonoidHom.ext
    intro g
    change ρ (α g) = ρ (ProjectiveLine.complementFundamentalAutomorphism K g)
    rw [hα]
  rw [hcomp] at H
  exact ⟨⟨H.trans ((F.complementMidpointMonodromyEquiv K).compHom π.ker.subtype).symm⟩,
    hAbs⟩

private theorem kernelResult_of_eq
    {L G V W : Type*} [Field L] [Group G]
    [AddCommGroup V] [Module L V] [AddCommGroup W] [Module L W]
    (ρ : Representation L G V) (σ : Representation L G W)
    (A B : Subgroup G) (h : A = B)
    (hA : Nonempty (Representation.Equiv (ρ.comp A.subtype) (σ.comp A.subtype)) ∧
      (Representation.baseChange (AlgebraicClosure L) (ρ.comp A.subtype)).IsIrreducible) :
    Nonempty (Representation.Equiv (ρ.comp B.subtype) (σ.comp B.subtype)) ∧
      (Representation.baseChange (AlgebraicClosure L) (ρ.comp B.subtype)).IsIrreducible := by
  subst B
  exact hA

/-- Transport generic local classes before applying the cusp comparison.
Keeping the base field abstract prevents reduction of its chosen arithmetic
presentation in the geometric linear-algebra proof. -/
theorem geometricComplementEquiv_of_genericCuspClasses
    (K Kgen L : Type) [Field K] [CharZero K] [Field Kgen]
    [NontriviallyNormedField L] [CompleteSpace L]
    (xgen : Spec (CommRingCat.of Kgen) ⟶ ProjectiveLine.punctured K)
    (pathIso : Scheme.finiteArithmeticFiberFunctor Kgen xgen ≅
      Scheme.finiteArithmeticFiberFunctor K
        (ProjectiveLine.puncturedPoint K (ProjectiveLine.midpointParameter K)))
    (τ : L) (hτ : τ ≠ 2)
    (F : Scheme.EtaleLocalSystem K (ProjectiveLine.punctured K) L)
    (Fgen : Scheme.EtaleLocalSystem Kgen (ProjectiveLine.punctured K) L)
    (ePath : Representation.Equiv
      (Scheme.fiberMonodromy Kgen (ProjectiveLine.punctured K)
        Fgen.algebraicFunctor xgen)
      ((puncturedFiberMonodromy K (ProjectiveLine.midpointParameter K) F).comp
        (Scheme.geometricFiberPathGroupEquiv Kgen K
          pathIso).toMonoidHom)) :
    let ξ₀ := ProjectiveLine.midpointParameter K
    let x := ProjectiveLine.puncturedPoint K ξ₀
    let π := Scheme.etaleFundamentalGroupMap (ProjectiveLine.puncturedToSpec K) K x
    let path := Scheme.geometricFiberPathGroupEquiv Kgen K
      pathIso
    ∀ (g : Fin 3 → Scheme.etaleFundamentalGroup Kgen
        xgen)
      (a b d : π.ker),
        path (g 0) = (a : Scheme.etaleFundamentalGroup K x) →
        path (g 1) = (b : Scheme.etaleFundamentalGroup K x) →
        path (g 2) = (d : Scheme.etaleFundamentalGroup K x) →
        a * b * d = 1 → Dense (Subgroup.closure ({a, b} : Set π.ker) : Set π.ker) →
        (∀ i, ∃ B : Module.Basis (Fin 2) L (Fgen.toFunctor.obj
          (Scheme.etaleFiberPoint Kgen (ProjectiveLine.punctured K)
            xgen)),
          LinearMap.toMatrix B B (Scheme.fiberMonodromy Kgen
            (ProjectiveLine.punctured K) Fgen.algebraicFunctor
            xgen (g i)) =
              (Monodromy.standardTriple τ i : Matrix (Fin 2) (Fin 2) L)) →
        ∀ (α : π.ker ≃ₜ* π.ker),
          (∀ g : π.ker, (α g : Scheme.etaleFundamentalGroup K x) =
            ProjectiveLine.complementFundamentalAutomorphism K g) → α a = b → α b = a →
      let k := (puncturedArithmeticProjectionHom K ξ₀).ker.subtype
      Nonempty (Representation.Equiv ((puncturedFiberMonodromy K ξ₀ F).comp k)
        ((puncturedFiberMonodromy K ξ₀ (F.complementPullback K L)).comp k)) ∧
        (Representation.baseChange (AlgebraicClosure L)
          ((puncturedFiberMonodromy K ξ₀ F).comp k)).IsIrreducible := by
  dsimp only
  intro g a b d hga hgb hgd hprod hdense hclasses α hα ha hb
  let ξ₀ := ProjectiveLine.midpointParameter K
  let x := ProjectiveLine.puncturedPoint K ξ₀
  let path := Scheme.geometricFiberPathGroupEquiv Kgen K
    pathIso
  let V := F.toFunctor.obj (Scheme.etaleFiberPoint K (ProjectiveLine.punctured K) x)
  let ρ : Representation L (Scheme.etaleFundamentalGroup K x) V :=
    puncturedFiberMonodromy K ξ₀ F
  let u : Fin 3 → Scheme.etaleFundamentalGroup K x := ![a, b, d]
  have hu : ∀ i, path (g i) = u i := by
    intro i
    fin_cases i
    · exact hga
    · exact hgb
    · exact hgd
  have htrans := localClasses_transport _ ρ path.toMonoidHom ePath g u hu
    (fun i => (Monodromy.standardTriple τ i : Matrix (Fin 2) (Fin 2) L)) hclasses
  obtain ⟨b₀, h0⟩ := htrans 0
  obtain ⟨b₁, h1⟩ := htrans 1
  obtain ⟨b₂, h2⟩ := htrans 2
  exact kernelResult_of_eq ρ (puncturedFiberMonodromy K ξ₀ (F.complementPullback K L))
    _ _ (puncturedArithmeticProjectionHom_ker K ξ₀).symm
    (complementEquiv_of_cusp_matrices K L F a b d hprod hdense α hα ha hb
      τ hτ b₀ b₁ b₂ h0 h1 h2)

end HilbertModularity.Hypergeometric
