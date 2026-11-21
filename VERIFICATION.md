# Verification and outstanding proof obligations

## Tests performed

- Lean 4.34.0 and the project's pinned Mathlib revision.
- Original project's November 20, 2026 audit: `lake build` succeeded with **5,693 jobs** and the 17-declaration axiom report completed.
- A Windows user independently reported `Build completed successfully (5693 jobs)`.
- Direct Windows `#print axioms` queries for the two named revised deep-cusp theorems reported **`[propext, sorryAx, Classical.choice, Quot.sound]`**.

The phrase “build completed” refers to typechecking the source under its imported assumptions. It does not mean that the full manuscript has an unconditional Lean proof.

## Headline modularity declarations

| Lean declaration | Axiom footprint | Interpretation |
| --- | --- | --- |
| `HilbertModularity.Hypergeometric.revisedPaperI_deepCusp_modular` | `propext`, **`sorryAx`**, `Classical.choice`, `Quot.sound` | Uses the earlier `finiteFieldHilbertModularAt_of_deep_cusp` theorem, so inherits its admitted literature inputs. |
| `HilbertModularity.Hypergeometric.revisedPaperI_cubicDivisibility_modular` | Same four axioms | Converts the cubic-divisibility condition to the earlier deep-cusp theorem; still conditional on the existing inputs. |

The previous AxiomProver audit traced **43** of its **72** admitted literature declarations to the original deep-cusp theorem's transitive proof terms. That historical dependency inventory was not recomputed for every new declaration in this public-release candidate; inspect the Lean report for each theorem.

## Mathematical claims not yet formally discharged

1. **Admitted literature interfaces.** `ASSUMPTIONS.md` records 72 named results with proofs terminated by `sorry`, including difficult geometry, Galois representations, and modularity lifting.
2. **Geometric pullback identifications.** The new exact-twist argument assumes `HasLabelledPullbacks` at a chosen place; conductor-lifting refinements use `HasConductorPullbacks`. The required equivariant maps from the actual common cover to the chosen RM and Euler representations remain to be constructed.
3. **Family-level exact twist.** Specialization under pullback assumptions is not equivalent to an unconditional generic family comparison.
4. **Strengthened RM automorphy/Hecke normalization.** The specified untwisted/twisted eigenform relation and Hecke-polynomial constant term are established under their particular pullback hypotheses and original admitted automorphy interfaces.

## Distinguish complete from conditional proofs

The executable file [`RevisedPaperIAxiomReport.lean`](RevisedPaperIAxiomReport.lean) queries 17 declarations. Some elementary arithmetic and character-sum results use only standard Lean axioms. Some geometric/cohomological and modularity declarations use `sorryAx` inherited from the original admitted interfaces. An absence of `sorry` in a *new theorem's source file* is not evidence that its transitive proof contains no `sorryAx`.

## Commands

```sh
lake exe cache get
lake build
lake env lean RevisedPaperIAxiomReport.lean
```

The same project can be audited with direct `#print axioms` queries. Keep the resulting logs with the publication record, but do not include large generated build caches in Git.
