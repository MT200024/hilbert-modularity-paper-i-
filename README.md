# Hilbert modularity of finite-field hypergeometric functions I — Lean 4

Lean code accompanying the prime-denominator Paper I by **Mohit Tripathi and Ankush Goswami**. The initial large-scale formalization was assembled by **AxiomProver**; this repository retains its underlying development and adds modules associated with the revised manuscript. See [ATTRIBUTION.md](ATTRIBUTION.md) and [PROVENANCE.md](PROVENANCE.md).

## Verification status

**Reproducible compilation; conditional formalization — not a complete, assumption-free proof of the manuscript.**

- Pinned Lean version: **4.34.0**; Mathlib revision is pinned in `lake-manifest.json`.
- The revised project completed **`lake build` successfully (5,693 jobs)** on November 20, 2026; the user also reproduced a successful build on Windows.
- The original development contains **72 `sorry`-admitted literature inputs**, explicitly indexed in [ASSUMPTIONS.md](ASSUMPTIONS.md). These remain present in the revised development.
- `#print axioms` on both revised main modularity theorems reports `propext`, **`sorryAx`**, `Classical.choice`, and `Quot.sound`. Hence their full proofs have **not** been checked by the Lean kernel independently of admitted inputs.
- The additional exact-quadratic-twist and strengthened RM automorphy results are **conditional on** geometric labelled-pullback hypotheses (`HasLabelledPullbacks` / `HasConductorPullbacks`). Those geometric comparisons remain to be established.
- Several finite-field identities, arithmetic calculations, signed-quotient formulas, and numerical computations are checked using only Lean's standard foundational axioms. Check the individual declarations in [RevisedPaperIAxiomReport.lean](RevisedPaperIAxiomReport.lean).

More detail: [VERIFICATION.md](VERIFICATION.md), [BUILD_STATUS.md](BUILD_STATUS.md), and [MANUSCRIPT_ALIGNMENT.md](MANUSCRIPT_ALIGNMENT.md).

## Repository contents

- [`HilbertModularity/`](HilbertModularity/) — Lean mathematical developments, including AxiomProver's original modules.
- [`HilbertModularity/Hypergeometric/RevisedPaperI.lean`](HilbertModularity/Hypergeometric/RevisedPaperI.lean) — restates the original deep-cusp theorem in the revised paper's notation and derives the cubic-divisibility version.
- [`HilbertModularity/PaperI/`](HilbertModularity/PaperI/) — added Paper I arithmetic, quotient, twist, automorphy, Hecke, and example modules.
- [`ASSUMPTIONS.md`](ASSUMPTIONS.md) — documented `sorry` admissions and mathematical citations.
- [`MANUSCRIPT_ALIGNMENT.md`](MANUSCRIPT_ALIGNMENT.md) — statement-by-statement relationship between the revised manuscript and Lean declarations.
- [`RevisedPaperIAxiomReport.lean`](RevisedPaperIAxiomReport.lean) — executable axiom report.
- [`PROVENANCE.md`](PROVENANCE.md) — original-vs-revised archive provenance and file-change summary.
- [`GITHUB_SETUP_WINDOWS.md`](GITHUB_SETUP_WINDOWS.md) — Windows publishing steps.

The manuscript-corrections PDF from the source archive is *intentionally excluded* from this code repository. The maintainer reports having permission to publish the AxiomProver-derived code. No open-source license terms are asserted here; see [ATTRIBUTION.md](ATTRIBUTION.md).

## Reproduce the Lean checks

From the repository root, with [Lean 4 / Elan](https://lean-lang.org/) installed:

```sh
lake exe cache get
lake build
lake env lean RevisedPaperIAxiomReport.lean
```

For Windows PowerShell, the [setup instructions](GITHUB_SETUP_WINDOWS.md) include a UTF-8-without-BOM check of the two main theorems (which avoids Lean parser errors).

## Scientific scope

The core results concern finite-field hypergeometric data of prime denominator, their geometric realizations, and conditional Hilbert modularity deductions for deep-cusp parameters. Successful compilation establishes acceptance of the *stated Lean declarations relative to their assumptions*; it does not validate the matching of every manuscript claim to a fully proved Lean theorem. The library's admitted inputs and conditional geometric comparisons are part of the public verification record.

## Attribution and reuse

Please credit the mathematical authors and the AxiomProver formalization work. The maintainer reports having obtained permission to publish the included code. This repository intentionally includes no `LICENSE` file because no specific open-source license terms have been supplied; public source availability does not itself grant reuse permissions.
