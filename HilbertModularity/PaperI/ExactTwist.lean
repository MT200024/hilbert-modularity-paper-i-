module
public import HilbertModularity.PaperI.DeckDifference
public import HilbertModularity.PaperI.CyclotomicTwist
public import HilbertModularity.Hypergeometric.EulerPlusAlgebraicComparison
public import HilbertModularity.RepresentationTheory.CompatibleSystemPromotion

/-! # The prime-level comparison at all coefficient places -/
public noncomputable section
namespace HilbertModularity.PaperI
open AlgebraicGeometry IsDedekindDomain HilbertModularity.Cyclotomic
open HilbertModularity.Hypergeometric HilbertModularity.HilbertModularForms
open scoped NumberField
variable (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (m : ℕ) (hmPos : 0 < m) (hmLt : m < p)

abbrev eulerFamily (ξ : ProjectiveLine.Parameter (realCyclotomicField p)) :=
  chosenCommonEulerCompatibleSystem p m (Fact.out : p.Prime) hp hmPos hmLt ξ
abbrev plusFamily (ξ : ProjectiveLine.Parameter (realCyclotomicField p)) :=
  primePlusCompatibleSystem p hp ξ (cyclotomicField p)
    (realCyclotomic_minpoly_splits_in_cyclotomic_extension p (cyclotomicField p))
    (coefficientEmbedding p m (eulerExponent_coprime_of_prime p m (Fact.out : p.Prime) hmPos hmLt)
      (cyclotomicField p) (realCyclotomicField_le p))
abbrev compParameter (ξ : ProjectiveLine.Parameter (realCyclotomicField p)) :=
  ProjectiveLine.complementParameter (realCyclotomicField p) ξ

variable (ξ : ProjectiveLine.Parameter (realCyclotomicField p))

/-- The remaining geometric premise at one coefficient place. Each representation
and the RM label are specified before the ambient cover space is chosen. -/
def HasLabelledPullbacks (w : HeightOneSpectrum (𝓞 (cyclotomicField p))) : Prop :=
  letI : Fact (1 < p) := ⟨by omega⟩
  let L := w.adicCompletion (cyclotomicField p)
  let a := algebraMap (cyclotomicField p) L ((root p)^m)
  ∃ (H : Type) (hH : AddCommGroup H), letI := hH
    ∃ mH : Module L H, letI := mH
      Nonempty (QuotientPullbacks ((eulerFamily p hp m hmPos hmLt ξ).action w)
        ((plusFamily p hp m hmPos hmLt (compParameter p ξ)).action w)
        ((plusFamily p hp m hmPos hmLt ξ).action w) (cyclotomicSign p L) a H)

/-- The two specialized isomorphisms of the exact-twist corollary. -/
theorem prime_exact_twist_of_pullbacks (w : HeightOneSpectrum (𝓞 (cyclotomicField p)))
    (geometric : HasLabelledPullbacks p hp m hmPos hmLt ξ w)
    (v : HeightOneSpectrum (𝓞 (cyclotomicField p))) :
    letI : Fact (1 < p) := ⟨by omega⟩
    let U := eulerFamily p hp m hmPos hmLt ξ
    let V := plusFamily p hp m hmPos hmLt (compParameter p ξ)
    let W := plusFamily p hp m hmPos hmLt ξ
    Nonempty ((U.action v).Equiv (V.action v)) ∧
      Nonempty ((V.action v).Equiv ((W.action v).characterTwist (cyclotomicSign p (v.adicCompletion (cyclotomicField p))))) := by
  let : Fact (1 < p) := ⟨by omega⟩
  let F := cyclotomicField p
  let L := w.adicCompletion F
  let a := algebraMap F L (root p ^ m)
  let U := eulerFamily p hp m hmPos hmLt ξ
  let V := plusFamily p hp m hmPos hmLt (compParameter p ξ)
  let W := plusFamily p hp m hmPos hmLt ξ
  let χ := algebraicCyclotomicSign p F
  have hc (v : HeightOneSpectrum (𝓞 F)) : χ.local v = cyclotomicSign p (v.adicCompletion F) := by
    rw [FiniteAlgebraicGaloisCharacter.local_eq_composition]
    exact algebraicCyclotomicSign_map p F _ _
  obtain ⟨H, iH, mH, ⟨D⟩⟩ := geometric
  have ha : IsPrimitiveRoot a p := ((root_isPrimitiveRoot p).pow_of_coprime m
    (eulerExponent_coprime_of_prime p m Fact.out hmPos hmLt)).map_of_injective (algebraMap F L).injective
  have ha0 := ha.ne_zero (NeZero.ne p)
  have hne : a ≠ a⁻¹ := by
    intro h
    have hs : a^2 = 1 := calc
      a^2 = a*a := pow_two _
      _ = a*a⁻¹ := congrArg (a * ·) h
      _ = 1 := mul_inv_cancel₀ ha0
    have hle := Nat.le_of_dvd (by decide : 0 < 2) ((ha.pow_eq_one_iff_dvd 2).mp hs)
    omega
  let T := D.complementTwist ha0 hne
  have promote (S : NumberFieldCompatibleSystem (realCyclotomicField p) F)
      (e : (S.action w).Equiv ((W.action w).characterTwist (cyclotomicSign p L))) :
      Nonempty ((S.action v).Equiv ((W.action v).characterTwist (cyclotomicSign p (v.adicCompletion F)))) := by
    rw [← hc w] at e
    obtain ⟨e'⟩ := S.promote_characterComparison W χ w (e.trans (Representation.characterTwistTensorEquiv _ _).symm) v
    rw [← hc v]
    exact ⟨e'.trans (Representation.characterTwistTensorEquiv _ _)⟩
  obtain ⟨eu⟩ := promote U (D.eulerComplement.trans T)
  obtain ⟨ev⟩ := promote V T
  exact ⟨⟨eu.trans ev.symm⟩, ⟨ev⟩⟩
end HilbertModularity.PaperI
