# Archive provenance and file comparison

This GitHub-ready source package was prepared from the following existing source archives:

- **Baseline:** `Hilbert-Modularity-Lean-Formalization (3)(2).zip` (AxiomProver-derived project).
- **Revised:** `Paper_I_Lean_4_34.zip` (revised Paper I project).

A byte-by-byte comparison of the files in those two archives showed:

- Original archive: **973** `.lean` source files.
- Revised archive: **988** `.lean` source files (**15 additional** `.lean` files).
- **21 files added** in total (including documentation and tools).
- **Three files changed** in place: `.gitignore`, `README.md`, and `HilbertModularity.lean` (the root imports).
- No baseline files removed; **all pre-existing Lean source files were byte-for-byte unchanged** in the revised archive.

This GitHub-ready copy changes only the top-level `README.md` and `.gitignore`, adds `ATTRIBUTION.md`, `VERIFICATION.md`, `PROVENANCE.md`, and `GITHUB_SETUP_WINDOWS.md`, and intentionally excludes `Hilbert-Manuscript-Corrections.pdf` from the public source-code release. **All 988 Lean source files are byte-for-byte identical to those in `Paper_I_Lean_4_34.zip`.**

The precise revised manuscript is referenced by `SOURCE_FINGERPRINTS.sha256`, which is retained unchanged. That file is historical provenance, not proof that an unpublished manuscript should automatically be posted.

## Publication status

The project has *not* been pushed to any GitHub account as part of this preparation. The maintainer reports publication permission; no specific open-source license has been provided, as explained in `ATTRIBUTION.md`.
