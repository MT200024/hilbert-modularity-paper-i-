/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.ProjectiveLine.Inertia
public import HilbertModularity.Geometry.Etale.GenericParameterInvolution
public import HilbertModularity.FieldTheory.RatFunc.InertiaComplementInverse

/-! # Complement exchanges actual finite-cusp inertia

The generic fundamental-group automorphism induced by `t ↦ 1-t` carries
inertia at `a` to a conjugate of inertia at `1-a`. In particular it exchanges
the two finite deleted cusps. This concerns inertia subgroups, without making
a choice of tame generators.
-/

@[expose] public noncomputable section
namespace AlgebraicGeometry.ProjectiveLine
universe u
variable (K : Type u) [Field K] [CharZero K]

/-- The actual generic complement automorphism exchanges finite-coordinate inertia up to conjugacy. -/
theorem puncturedAffineInertia_complement_conjugate (a : K) :
    ∃ g : Scheme.etaleFundamentalGroup (RatFunc K) (puncturedRationalPoint K),
      (puncturedAffineInertia K a).map
        (genericComplementFundamentalAutomorphism K).toMulEquiv.toMonoidHom =
        (puncturedAffineInertia K (1 - a)).map (MulAut.conj g).toMonoidHom := by
  let q := Scheme.galoisToEtaleFundamentalGroup (RatFunc K) (puncturedRationalPoint K)
  let φ := AlgebraicClosure.galoisFieldEquiv (RatFunc K) (RatFunc K)
    (RatFunc.complementAlgEquiv K).toRingEquiv
  let F := (genericComplementFundamentalAutomorphism K).toMulEquiv.toMonoidHom
  obtain ⟨g, hg⟩ := RatFunc.affineInertia_complement_symm_conjugate K a
  refine ⟨q g, ?_⟩
  have hmap : ((RatFunc.affineInertia K a).map q).map F =
      ((RatFunc.affineInertia K a).map φ.symm.toMonoidHom).map q := by
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    apply MonoidHom.ext
    intro σ
    exact genericComplementFundamentalAutomorphism_galois K σ
  change ((RatFunc.affineInertia K a).map q).map F =
    ((RatFunc.affineInertia K (1 - a)).map q).map (MulAut.conj (q g)).toMonoidHom
  rw [hmap, hg, Subgroup.map_map, Subgroup.map_map]
  congr 1
  apply MonoidHom.ext
  intro σ
  change q (g * σ * g⁻¹) = q g * q σ * (q g)⁻¹
  simp only [map_mul, map_inv]

/-- Complement carries actual inertia at zero to a conjugate of inertia at one. -/
theorem puncturedZeroInertia_complement_conjugate :
    ∃ g : Scheme.etaleFundamentalGroup (RatFunc K) (puncturedRationalPoint K),
      (puncturedAffineInertia K 0).map
        (genericComplementFundamentalAutomorphism K).toMulEquiv.toMonoidHom =
        (puncturedAffineInertia K 1).map (MulAut.conj g).toMonoidHom := by
  simpa only [sub_zero] using puncturedAffineInertia_complement_conjugate K 0

/-- Complement carries actual inertia at one to a conjugate of inertia at zero. -/
theorem puncturedOneInertia_complement_conjugate :
    ∃ g : Scheme.etaleFundamentalGroup (RatFunc K) (puncturedRationalPoint K),
      (puncturedAffineInertia K 1).map
        (genericComplementFundamentalAutomorphism K).toMulEquiv.toMonoidHom =
        (puncturedAffineInertia K 0).map (MulAut.conj g).toMonoidHom := by
  simpa only [sub_self] using puncturedAffineInertia_complement_conjugate K 1

end AlgebraicGeometry.ProjectiveLine
