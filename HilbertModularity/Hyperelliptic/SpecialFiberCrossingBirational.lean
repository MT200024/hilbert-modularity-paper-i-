/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hyperelliptic.SpecialFiberCrossingFiberProduct

/-! # The two branches agree with the crossing away from its parameter

The diagonal parameter belongs to the crossing ring. It is regular when the
branch ring is a domain, and one multiplication by it takes every pair of
branch functions back into the crossing ring. These are the birational inputs
for identifying the product of branches with the local normalization.
-/

public noncomputable section

open Polynomial

namespace HilbertModularity.Hyperelliptic

/-- The diagonal local parameter in the fibre product of two branches. -/
def localNodeParameter {S : Type*} [CommRing S] (t : S) : localNodePairs t :=
  ⟨(t, t), (mem_localNodePairs_iff_dvd t _).mpr (by simp)⟩

/-- One multiplication by the diagonal parameter clears the branch mismatch. -/
theorem localNodePairs_parameter_clears_denominators {S : Type*} [CommRing S]
    (t : S) (z : S × S) :
    ∃ a : localNodePairs t,
      (algebraMap (localNodePairs t) (S × S)) a =
        z * (algebraMap (localNodePairs t) (S × S)) (localNodeParameter t) := by
  refine ⟨⟨(t * z.1, t * z.2), localNodePairs_parameter_mul_mem t z⟩, ?_⟩
  change (t * z.1, t * z.2) = z * (t, t)
  ext <;> simp [mul_comm]

/-- The diagonal parameter is regular in the branch product. -/
theorem localNodeProduct_parameter_regular {S : Type*} [CommRing S] [IsDomain S]
    (t : S) (ht : t ≠ 0) : (t, t) ∈ nonZeroDivisors (S × S) := by
  rw [mem_nonZeroDivisors_iff]
  constructor
  · intro z hz
    have h₁ : t * z.1 = 0 := congrArg Prod.fst hz
    have h₂ : t * z.2 = 0 := congrArg Prod.snd hz
    exact Prod.ext ((mul_eq_zero.mp h₁).resolve_left ht)
      ((mul_eq_zero.mp h₂).resolve_left ht)
  · intro z hz
    have h₁ : z.1 * t = 0 := congrArg Prod.fst hz
    have h₂ : z.2 * t = 0 := congrArg Prod.snd hz
    exact Prod.ext ((mul_eq_zero.mp h₁).resolve_right ht)
      ((mul_eq_zero.mp h₂).resolve_right ht)

/-- The diagonal parameter is also regular in the crossing ring. -/
theorem localNodeParameter_regular {S : Type*} [CommRing S] [IsDomain S]
    (t : S) (ht : t ≠ 0) :
    localNodeParameter t ∈ nonZeroDivisors (localNodePairs t) := by
  rw [mem_nonZeroDivisors_iff]
  constructor
  · intro a ha
    apply Subtype.ext
    have h := congrArg Subtype.val ha
    apply Prod.ext
    · have h₁ : t * a.1.1 = 0 := congrArg Prod.fst h
      exact (mul_eq_zero.mp h₁).resolve_left ht
    · have h₂ : t * a.1.2 = 0 := congrArg Prod.snd h
      exact (mul_eq_zero.mp h₂).resolve_left ht
  · intro a ha
    apply Subtype.ext
    have h := congrArg Subtype.val ha
    apply Prod.ext
    · have h₁ : a.1.1 * t = 0 := congrArg Prod.fst h
      exact (mul_eq_zero.mp h₁).resolve_right ht
    · have h₂ : a.1.2 * t = 0 := congrArg Prod.snd h
      exact (mul_eq_zero.mp h₂).resolve_right ht

/-- The local ring on each branch of a finite crossing is integrally closed. -/
theorem finiteCrossing_branch_isIntegrallyClosed {k : Type*} [Field k] (x : k) :
    IsIntegrallyClosed (Localization.AtPrime (RingHom.ker (evalRingHom x))) := by
  infer_instance

/-- The crossing ring acts on the product of branches after inverting the
diagonal local parameter, through its inclusion into the product. -/
@[instance_reducible] noncomputable def localNodeProductAwayAlgebra
    {S : Type*} [CommRing S] (t : S) :
    Algebra (localNodePairs t) (Localization.Away (t, t)) :=
  ((algebraMap (S × S) (Localization.Away (t, t))).comp
    (algebraMap (localNodePairs t) (S × S))).toAlgebra

/-- After inverting the crossing parameter, every branch function comes from
the crossing ring. This is the local birational comparison. -/
theorem localNodePairs_away_isLocalization {S : Type*} [CommRing S] [IsDomain S]
    (t : S) (ht : t ≠ 0) :
    letI := localNodeProductAwayAlgebra t
    IsLocalization.Away (localNodeParameter t) (Localization.Away (t, t)) := by
  let := localNodeProductAwayAlgebra t
  apply IsLocalization.Away.mk (localNodeParameter t)
  · change IsUnit (algebraMap (S × S) (Localization.Away (t, t)) (t, t))
    exact IsLocalization.Away.algebraMap_isUnit (x := (t, t))
  · intro z
    obtain ⟨n, b, hb⟩ := IsLocalization.Away.surj (x := (t, t)) z
    obtain ⟨a, ha⟩ := localNodePairs_parameter_clears_denominators t b
    refine ⟨n + 1, a, ?_⟩
    change z * (algebraMap (S × S) (Localization.Away (t, t)) (t, t)) ^ (n + 1) =
      algebraMap (S × S) (Localization.Away (t, t)) a.1
    rw [pow_succ, ← mul_assoc, hb, ← map_mul]
    change a.1 = b * (t, t) at ha
    exact congrArg (algebraMap (S × S) (Localization.Away (t, t))) ha.symm
  · intro a b hab
    have hregular := localNodeProduct_parameter_regular t ht
    have hM : Submonoid.powers (t, t) ≤ nonZeroDivisors (S × S) := by
      intro c hc
      obtain ⟨n, rfl⟩ := hc
      exact pow_mem hregular n
    have hinj : Function.Injective
        (algebraMap (S × S) (Localization.Away (t, t))) :=
      IsLocalization.injective (Localization.Away (t, t)) hM
    have hab' : a = b := by
      apply Subtype.ext
      apply hinj
      exact hab
    exact ⟨0, by simp [hab']⟩

end HilbertModularity.Hyperelliptic
