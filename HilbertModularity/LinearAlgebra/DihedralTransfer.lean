/- Assembled by AxiomProver. -/

module

public import HilbertModularity.LinearAlgebra.DihedralEigenspace

/-! # Transfer through a reflection quotient

The identities `r p = 2` and `p r = 1 + s` identify the quotient space with the
reflection-fixed space. This is the linear-algebra transfer used in the quotient
construction of [GPRV, Proposition 9.5]; existence of geometric maps satisfying
these identities is a separate matter.
-/

public noncomputable section

namespace HilbertModularity

variable {L V W : Type*} [Field L] [AddCommGroup V] [Module L V]
  [AddCommGroup W] [Module L W]

/-- Linear pullback and trace maps obeying the degree-two quotient identities. -/
structure DihedralTransfer (d : DihedralAction L V) where
  p : W →ₗ[L] V
  r : V →ₗ[L] W
  r_p : ∀ w, r (p w) = (2 : L) • w
  p_r : ∀ v, p (r v) = v + d.reflection v

namespace DihedralTransfer

variable {d : DihedralAction L V} (t : DihedralTransfer (W := W) d)

theorem reflection_p (w : W) : d.reflection (t.p w) = t.p w := by
  have h := t.p_r (t.p w)
  rw [t.r_p, map_smul, two_smul] at h
  exact (add_left_cancel h).symm

theorem r_reflection (v : V) : t.r (d.reflection v) = t.r v := by
  have h := congrArg t.r (t.p_r v)
  rw [t.r_p, map_add, two_smul] at h
  exact (add_left_cancel h).symm

theorem p_injective (htwo : (2 : L) ≠ 0) : Function.Injective t.p := by
  intro x y h
  have hr := congrArg t.r h
  rw [t.r_p, t.r_p] at hr
  calc
    x = (2 : L)⁻¹ • ((2 : L) • x) := by
      rw [smul_smul, inv_mul_cancel₀ htwo, one_smul]
    _ = (2 : L)⁻¹ • ((2 : L) • y) := congrArg _ hr
    _ = y := by rw [smul_smul, inv_mul_cancel₀ htwo, one_smul]

/-- Pullback identifies the quotient with the reflection-fixed subspace. -/
def fixedSpaceEquiv (htwo : (2 : L) ≠ 0) : W ≃ₗ[L] d.fixedSpace where
  toFun w := ⟨t.p w, by
    apply (d.mem_fixedSpace_iff (t.p w)).mpr
    exact t.reflection_p w⟩
  invFun v := (2 : L)⁻¹ • t.r v
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp
  left_inv w := by
    change (2 : L)⁻¹ • t.r (t.p w) = w
    rw [t.r_p, smul_smul, inv_mul_cancel₀ htwo, one_smul]
  right_inv v := by
    apply Subtype.ext
    have hs : d.reflection (v : V) = v := by
      exact (d.mem_fixedSpace_iff v).mp v.property
    change t.p ((2 : L)⁻¹ • t.r v) = v
    rw [map_smul, t.p_r, hs]
    calc
      (2 : L)⁻¹ • ((v : V) + v) = (2 : L)⁻¹ • ((2 : L) • v) := by
        rw [two_smul]
      _ = v := by rw [smul_smul, inv_mul_cancel₀ htwo, one_smul]

theorem fixedSpaceEquiv_apply (htwo : (2 : L) ≠ 0) (w : W) :
    ((t.fixedSpaceEquiv htwo w : d.fixedSpace) : V) = t.p w := (rfl)

theorem fixedSpaceEquiv_symm_apply (htwo : (2 : L) ≠ 0)
    (v : d.fixedSpace) :
    (t.fixedSpaceEquiv htwo).symm v = (2 : L)⁻¹ • t.r v := (rfl)

/-- The quotient operator obtained by transferring `δ + δ⁻¹`. -/
def quotientOperator : Module.End L W where
  toFun w := (2 : L)⁻¹ • t.r (d.realOperator (t.p w))
  map_add' x y := by
    rw [map_add, map_add, map_add, smul_add]
  map_smul' c x := by
    change (2 : L)⁻¹ • t.r (d.realOperator (t.p (c • x))) =
      c • ((2 : L)⁻¹ • t.r (d.realOperator (t.p x)))
    rw [map_smul, map_smul, map_smul, smul_comm]

/-- Pullback intertwines the transferred operator and the real deck operator. -/
theorem p_quotientOperator (htwo : (2 : L) ≠ 0) (w : W) :
    t.p (t.quotientOperator w) = d.realOperator (t.p w) := by
  change t.p ((2 : L)⁻¹ • t.r (d.realOperator (t.p w))) =
    d.realOperator (t.p w)
  have hfixed : d.reflection (d.realOperator (t.p w)) =
      d.realOperator (t.p w) := by
    rw [← d.realOperator_reflection, t.reflection_p]
  rw [map_smul, t.p_r, hfixed]
  calc
    (2 : L)⁻¹ • (d.realOperator (t.p w) + d.realOperator (t.p w)) =
        (2 : L)⁻¹ • ((2 : L) • d.realOperator (t.p w)) := by
      rw [two_smul]
    _ = d.realOperator (t.p w) := by
      rw [smul_smul, inv_mul_cancel₀ htwo, one_smul]

private theorem p_mem_realEigenspace (htwo : (2 : L) ≠ 0) (a : L)
    {w : W} (hw : w ∈ Module.End.eigenspace t.quotientOperator (a + a⁻¹)) :
    t.p w ∈ d.realEigenspace a := by
  apply (d.mem_realEigenspace_iff a (t.p w)).mpr
  constructor
  · exact t.reflection_p w
  · have heig := Module.End.mem_eigenspace_iff.mp hw
    have h := congrArg t.p heig
    rw [t.p_quotientOperator htwo, map_smul] at h
    exact h

/-- Eigenspace transfer through a degree-two quotient. The forward map is
`r(v)` and the inverse is `(a-a⁻¹)⁻¹ • (δ(pw)-a⁻¹ • pw)`. -/
def deckEigenspaceEquiv (htwo : (2 : L) ≠ 0) (a : L)
    (ha : a ≠ 0) (hne : a ≠ a⁻¹) :
    d.deckEigenspace a ≃ₗ[L]
      Module.End.eigenspace t.quotientOperator (a + a⁻¹) where
  toFun v := ⟨t.r v, by
    apply Module.End.mem_eigenspace_iff.mpr
    apply t.p_injective htwo
    rw [t.p_quotientOperator htwo, map_smul, t.p_r]
    have h := (d.mem_realEigenspace_iff a _).mp
      (d.deckEigenspaceEquiv a ha hne v).property
    rw [d.deckEigenspaceEquiv_apply] at h
    exact h.2⟩
  invFun w := ⟨(a - a⁻¹)⁻¹ • (d.delta (t.p w) - a⁻¹ • t.p w), by
    let w' : d.realEigenspace a :=
      ⟨t.p w, t.p_mem_realEigenspace htwo a w.property⟩
    have h := ((d.deckEigenspaceEquiv a ha hne).symm w').property
    rw [d.deckEigenspaceEquiv_symm_apply] at h
    exact h⟩
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp
  left_inv v := by
    apply Subtype.ext
    have h := congrArg (fun x : d.deckEigenspace a => (x : V))
      ((d.deckEigenspaceEquiv a ha hne).left_inv v)
    change (((d.deckEigenspaceEquiv a ha hne).symm
      (d.deckEigenspaceEquiv a ha hne v) : d.deckEigenspace a) : V) = v at h
    rw [d.deckEigenspaceEquiv_symm_apply,
      d.deckEigenspaceEquiv_apply] at h
    change (a - a⁻¹)⁻¹ •
      (d.delta (t.p (t.r v)) - a⁻¹ • t.p (t.r v)) = v
    rw [t.p_r]
    exact h
  right_inv w := by
    apply Subtype.ext
    apply t.p_injective htwo
    rw [t.p_r]
    have h := congrArg (fun x : d.realEigenspace a => (x : V))
      ((d.deckEigenspaceEquiv a ha hne).right_inv
        ⟨t.p w, t.p_mem_realEigenspace htwo a w.property⟩)
    change ((d.deckEigenspaceEquiv a ha hne
      ((d.deckEigenspaceEquiv a ha hne).symm
        ⟨t.p w, t.p_mem_realEigenspace htwo a w.property⟩) :
          d.realEigenspace a) : V) = t.p w at h
    rw [d.deckEigenspaceEquiv_apply,
      d.deckEigenspaceEquiv_symm_apply] at h
    exact h

theorem deckEigenspaceEquiv_apply (htwo : (2 : L) ≠ 0) (a : L)
    (ha : a ≠ 0) (hne : a ≠ a⁻¹) (v : d.deckEigenspace a) :
    ((t.deckEigenspaceEquiv htwo a ha hne v :
      Module.End.eigenspace t.quotientOperator (a + a⁻¹)) : W) = t.r v := (rfl)

theorem deckEigenspaceEquiv_symm_apply (htwo : (2 : L) ≠ 0) (a : L)
    (ha : a ≠ 0) (hne : a ≠ a⁻¹)
    (w : Module.End.eigenspace t.quotientOperator (a + a⁻¹)) :
    (((t.deckEigenspaceEquiv htwo a ha hne).symm w : d.deckEigenspace a) : V) =
      (a - a⁻¹)⁻¹ • (d.delta (t.p w) - a⁻¹ • t.p w) := (rfl)

end DihedralTransfer

end HilbertModularity
