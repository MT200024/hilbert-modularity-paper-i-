# Build and proof audit

Verified on November 20, 2026 with Lean **4.34.0** on x86-64 Linux. The Lean release commit is `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b` and the pinned mathlib commit is `5ed2965256430c3649e86755f9576b54eca72435`.

| Command | Result |
| --- | --- |
| `lake build` | Exit code 0. Build completed successfully (5693 jobs). |
| `lake env lean RevisedPaperIAxiomReport.lean` | Exit code 0. Axiom lists printed for all 17 declarations. |
| `python3 static_source_audit.py` | 988 Lean files and 2,784 project import references. All project imports resolve. |

The source audit counted 72 existing `sorry` admissions documented in [ASSUMPTIONS.md](ASSUMPTIONS.md). The revised proof modules add no `sorry` or custom axioms. The axiom report confirms that the arithmetic normalizations, signed quotient equations, invariant-field generation, cyclotomic fixed field and Frobenius sign, auxiliary valuations, and the finite-field count and character-sum calculations at 19 use Lean's standard axioms. The modularity, promotion, and cohomological Frobenius-polynomial declarations report `sorryAx` through original literature inputs.

The specialized exact twist, the specified twisted eigenform, and the strengthened Hecke formula are checked under their stated pullback hypotheses. See [MANUSCRIPT_ALIGNMENT.md](MANUSCRIPT_ALIGNMENT.md) for the remaining geometric and generic comparisons.
