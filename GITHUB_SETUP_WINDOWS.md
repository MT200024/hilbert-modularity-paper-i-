# Publishing this repository from Windows PowerShell

The GitHub release candidate is a complete project folder. **Do not copy Mathlib downloads or the `.lake` build directory into GitHub.**

## Before publishing

1. Read `ATTRIBUTION.md`, `VERIFICATION.md`, `ASSUMPTIONS.md`, and `MANUSCRIPT_ALIGNMENT.md`.
2. The maintainer reports that public redistribution permission has been obtained. Retain that permission record; add a `LICENSE` file only if specific license terms have been authorized.
3. Confirm that every file is suitable for public release. The manuscript-corrections PDF was intentionally excluded.

## Open the prepared project

Download and extract the GitHub-ready ZIP into your Downloads folder. Open a **new PowerShell window** and run:

```powershell
cd "$HOME\Downloads\hilbert-modularity-paper-i"
lake --version
```

You should be inside the folder that contains `lakefile.toml`, `lean-toolchain`, and `HilbertModularity`.

## Optional: Verify the project again

```powershell
lake exe cache get
lake build
lake env lean RevisedPaperIAxiomReport.lean
```

The first command downloads the pinned Mathlib cache if needed; the first build on a newly extracted folder can take substantial resources. These steps are optional if you are relying on the supplied prior build record, but recommended before announcing a public release.

To create a temporary report with no UTF-8 byte-order mark using Windows PowerShell 5.1 or 7:

```powershell
$lines = @(
  'import HilbertModularity.Hypergeometric.RevisedPaperI',
  '#print axioms HilbertModularity.Hypergeometric.revisedPaperI_deepCusp_modular',
  '#print axioms HilbertModularity.Hypergeometric.revisedPaperI_cubicDivisibility_modular'
)
[System.IO.File]::WriteAllLines(
  (Join-Path (Get-Location) 'CheckAxioms.lean'),
  $lines,
  [System.Text.UTF8Encoding]::new($false)
)
lake env lean CheckAxioms.lean
```

## Publish the public repository

On GitHub, choose **New repository**, use the name `hilbert-modularity-paper-i`, and set the visibility to **Public**. Do **not** initialize it with a README, `.gitignore`, or license (the local directory already contains the first two, and license terms have not been specified).

If Git for Windows is installed, enter these commands from this directory:

```powershell
git --version
git init -b main
git add .
git status --short
git commit -m "Initial public release: conditional Paper I Lean formalization"
git remote add origin https://github.com/YOUR_GITHUB_USERNAME/hilbert-modularity-paper-i.git
git push -u origin main
```

Replace `YOUR_GITHUB_USERNAME` with your actual GitHub account name. GitHub may prompt you to sign in. The generated build cache `.lake/` and local axiom logs are ignored by `.gitignore`.

If `git init -b main` is not supported by an older installed Git version, use `git init` followed by `git branch -M main` before `git add .`.

You can instead use GitHub Desktop to publish the extracted repository; review staged files before committing.

## Important

Preparing this ZIP **does not automatically create a remote repository or upload anything to GitHub**. Please do not describe the project as fully verified in Lean: the headline modularity results have `sorryAx` dependencies and the exact-twist conclusions are conditional on stated geometric pullback hypotheses.
