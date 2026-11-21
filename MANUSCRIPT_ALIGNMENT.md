# Lean coverage for the revised Paper I

The source is the LaTeX entitled *Hilbert Modularity of Finite-Field Hypergeometric Functions I* attached on November 20, 2026. The SHA-256 in [SOURCE_FINGERPRINTS.sha256](SOURCE_FINGERPRINTS.sha256) identifies the exact text. The statements below use the numbering in that text.

| Manuscript item | Lean declaration or module | Coverage |
| --- | --- | --- |
| Proposition 2.4, the McCarthy–GPRV normalization | `Cyclotomic.mccarthyValue_eq_gprvValue` and `Hypergeometric.symmetricMcCarthySum_eq_gprvSymmetricSum` | The finite-sum identities include the inverse convention for the power-residue character. |
| Lemma 2.5, the direct Euler sum | `Hypergeometric.rankTwoMcCarthySum_eq_eulerCharacterSum` | The theorem retains the factor `-A(-1)`. See `Hypergeometric.EulerSum`. |
| Theorem 3.3 and Lemma 3.5, finite comparison character and promotion | `Hypergeometric.exists_algebraic_character_comparing_chosenEffectiveEuler` and `Hypergeometric.exists_chosenEuler_twistedPlus_at_all_places` | The earlier comparison produces a finite-order character. The compatible-system argument promotes the comparison across coefficient places. |
| Corollary 3.4, the signed quotients and exact twist | `PaperI.EulerChart`, `PaperI.QuotientFields`, `PaperI.DeckDifference`, `PaperI.CyclotomicTwist`, and `PaperI.prime_exact_twist_of_pullbacks` | The chart and invariant-field proofs identify the signed equations. The operator \(S-S^{-1}\) supplies the specialized comparison at every place given `HasLabelledPullbacks` at one place. The geometric identification and the generic intertwiner line remain open. |
| Theorem 1.2(i), untwisted RM eigenform | `PaperI.exists_rmEigenform_of_cubic` | Uses the library's conductor-place RM and Skinner–Wiles inputs, in the cohomological convention. |
| Theorem 1.2(ii), the twist of that eigenform | `PaperI.rm_and_twistedEuler_of_cubic_of_pullbacks` | Specifies the adelic twist of the same eigenform and identifies it at all coefficient places, under the labelled pullbacks at the lifting place. |
| Proposition 3.17, residual characters | `Hypergeometric.ChosenEulerResidual` | The original Lean results identify the RM constituents and the ratio on the effective Euler system. The exact twist in the paper's effective pair uses Corollary 3.4. |
| Theorem 1.1, Theorems 3.21–3.22, deep-cusp Hilbert modularity | `Hypergeometric.revisedPaperI_cubicDivisibility_modular`, `Hypergeometric.exists_chosenEuler_allPlaceEigenform_of_cubic`, and `PaperI.exists_norm_hecke_traces_of_cubic_of_pullbacks` | The cubic-divisibility conditions imply the library's modularity predicate using its original Hecke polynomial. The strengthened Hecke polynomial with constant term \(\mathrm{N}\mathfrak q\) uses the labelled pullbacks at the lifting place. |
| Remark 3.23, the auxiliary-prime example | `PaperI.cubic_parameter_auxiliary_valuations` and `PaperI.example_parameter_and_clearing` | Verifies the valuation formula at all \(q\ne p\) for \(p^3/(p^3+1)\), with the concrete denominator clearing at \(125/126\). |
| Example 3.24 at 11 and 41 | `Examples.PrimeFiveJointSelectedEvaluation` and related modules | The original split-prime examples use the project's literature inputs and selected arithmetic embeddings. |
| Example 3.24 at 19 | `PaperI.Nineteen.mccarthy_at_nineteen`, `projective_counts`, `geometricFrobeniusPolynomial_19` | Checks the oriented character sum and the projective counts \(25,423\). The Frobenius polynomial uses the original genus-two cohomology input. The identification with the chosen global twisted eigenform uses the exact comparison of Corollary 3.4. |

Namespace prefixes in this table are relative to `HilbertModularity`. Proof and admission information is in [ASSUMPTIONS.md](ASSUMPTIONS.md) and the executable report `RevisedPaperIAxiomReport.lean`.

## The remaining geometric comparison

For a specialization and one coefficient place, `HasLabelledPullbacks` asks for Galois-equivariant pullback identifications on one common cohomology space. The effective Euler representation and the plus RM factor at \(1-\xi\) belong to the negative eigenspace of the reflection on that space. The plus RM factor at \(\xi\) belongs to the positive eigenspace. The deck operator has the specified RM label \(\zeta_p^m+\zeta_p^{-m}\), and Galois conjugates the rotation according to the character of \(F_p/K_p\). The Lean code derives the specialized isomorphisms from that data.

The lifting and Hecke-normalization statements use `HasConductorPullbacks`. This is the same kind of diagram at the place above \(p\), with the third pullback defined on the native dual Tate representation used by Skinner–Wiles.

The supplied library chooses the plus Jacobian and its RM action. Its interface for the Darmon–Mestre endomorphism result gives a full-ring isomorphism. Linking that chosen RM action with the correspondence \(S+S^{-1}\) on the common cover and constructing the equivariant pullbacks are the remaining steps. The generic statement requires the corresponding comparison on the family.
