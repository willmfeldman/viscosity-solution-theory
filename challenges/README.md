# Comparator Challenges

This directory contains release comparator workspaces for the public
ViscositySolns API. Each subdirectory is a standalone Lake workspace with:

- `Vocabulary.lean` (in two workspaces also `Vocabulary/*.lean`; see below):
  the restated project definitions, importing `Mathlib` only. This is the copy
  that is edited.
- `Challenge.lean`: trusted statement surface. Its block between
  `-- BEGIN GENERATED VOCABULARY` and `-- END GENERATED VOCABULARY` is generated
  from the vocabulary files by `python3 scripts/challenge-prep.py sync`; below it
  are the theorem statements, with `sorry` proofs. In `ishii-lemma` and
  `semijet-testfunction` it instead imports the split vocabulary files (see below).
- `Solution.lean`: solution proof, importing `ViscositySolns`.
- `config.json`: comparator module names, theorem names, and permitted axioms.
- `lakefile.toml`: local workspace metadata pinned through the parent project.

The challenge vocabulary restates all project-local definitions against
`Mathlib` only (semijets, viscosity sub/supersolutions, properness, the Ishii structural
condition, Dirichlet barriers), rather than importing the library, so a
referee can verify the meaning of each statement without reading the library.
The `Solution.lean` files discharge the same theorem names through the public
library import.

The inline definitions reuse the library's names, so Comparator also checks
that each one is exactly the library's definition. That check compares the
names of the small auxiliary proofs Lean creates inside definitions (for
example for the numeral `2`), and Lean shares those proofs only within a file.
Their numbering therefore follows the library's module boundaries, and copying
several library modules' definitions into one file would rename some of them.
For this reason `ishii-lemma` splits its vocabulary into `Vocabulary/Basic.lean`
and `Vocabulary/Ishii.lean`, and `semijet-testfunction` into
`Vocabulary/Foundation.lean`, `Vocabulary/Smooth.lean`, and
`Vocabulary/Characterization.lean`, following the library's file boundaries. In
these two workspaces `Challenge.lean` imports those files (marked
`-- challenge-prep: split vocabulary`) instead of carrying a generated copy, and
the root `Vocabulary.lean` only re-exports them. `Vocabulary/Smooth.lean` also
restates two library definitions,
`gradientLinearMap` and `linearMapGradientCLM`, that no statement uses. They are
there only so that the auxiliary proofs reused by `bilinearMapHessian` carry
the library's names. Every file still imports `Mathlib` only.

## Challenge set

| Directory | Paper statement | Library theorem used by the solution |
|---|---|---|
| `comparison-compact` | Specialized boundary comparison on compact closure, with a uniform scalar-decrease hypothesis. Seven further theorems check the vocabulary, not headline results: zero-operator and zero-jet non-vacuity, positive-operator sign rejection, the `1/2` Hessian convention of the quadratic model (`‖y‖²` has superjet Hessian `2 • 1`, not `1`), and the orientation of degenerate ellipticity (`-trace X` is, `trace X` is not) | `comparison_of_constantShift_boundary_of_aleksandrov` + external Aleksandrov; the checks use the public semijet, viscosity-solution, and ellipticity definitions |
| `uniqueness` | Two-sided uniqueness corollary; largely reuses the comparison result | `eqOn_of_comparisonConclusions` over the boundary comparison theorem |
| `ishii-lemma` | User's Guide Thm 3.2 (Crandall–Ishii lemma for the quadratic penalty `(α/2)‖x-y‖²`, i.e. `ε = 1/α`, with the `3α` block bounds of CIL (3.10)) | `QuadraticPenaltyIshiiLemmaOn.of_aleksandrov` + external Aleksandrov |
| `jensen-lemma` | User's Guide Lemma A.3 (localized Jensen contact-set lemma) | `JensenContactSetPositiveMeasureOnClosedBallTheorem.proof` |
| `perron-existence` | Perron assembly for Dirichlet data `g` under a strong packaged hypothesis interface, with boundary equal to `frontier C` and Dirichlet semicontinuity on `C ∪ boundary`; this is not a direct challenge of the conventional CIL Theorem 4.1 hypotheses. The hypotheses are satisfiable non-trivially: the `harmonic-dirichlet` solution discharges them for the Laplacian with Lipschitz data | `PerronMethodExistenceTheorem.strictBoundary` |
| `semijet-testfunction` | Semijet / globally smooth `C²` test-function equivalence on an open domain, with the stated Hessian-continuity and symmetry assumptions | `viscositySubsolution_iff_smoothTestFunctionSubsolution` and the supersolution analogue |
| `harmonic-dirichlet` | Dirichlet problem for harmonic functions (Gilbarg–Trudinger Thm 2.14 with §2.8 barriers) on bounded `C²` domains, uniform-exterior-sphere domains, and balls, with a boundary modulus uniform over Lipschitz data; stated with Mathlib's `EuclideanSpace` and Laplacian only | `dirichlet_harmonic_modulus_of_uniformExteriorSphere` (Perron + Laplace comparison + barriers + Weyl's lemma) |

The comparison, uniqueness, and Ishii solutions consume the Aleksandrov
second-differentiability theorem through the pinned external
`AleksandrovDifferentiability` package
(`AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem.proof_external`),
so a comparator run on these challenges also transitively audits that
project. The Jensen lemma is proved internally and unconditionally.

## Toolchain

- Lean: `leanprover/lean4:v4.35.0-rc3`
- Mathlib: `v4.35.0-rc3`
- AleksandrovDifferentiability: release `v0.4.0`, pinned through the parent
  `lake-manifest.json`
- Comparator: `leanprover/comparator`, with a `lean4export` build matching Lean
  `v4.35.0-rc3` and the pinned `landrun` revision; the release workflow runs on a
  standard GitHub-hosted Linux runner. The workflow builds every dependency
  from source rather than from prebuilt release archives.

Every workspace sets `packagesDir = "../../.lake/packages"` in its
`lakefile.toml` (and records the same folder in its `lake-manifest.json`), so
all seven share the root workspace's dependency checkouts and builds instead
of each holding a separate multi-gigabyte copy. The manifests lock the same
revisions as the root manifest.

Repository CI builds the full library and its API smoke target, validates the
manifest against every challenge configuration and workspace inventory, and
checks headline declaration names and axioms. On every push it also elaborates
the Vocabulary, Challenge, and Solution targets of all seven workspaces with
`scripts/build-challenges.sh --trusted-all`, and `scripts/challenge-prep.py check`
confirms that every generated vocabulary block is up to date. That shows each file compiles against the current library; it
does not compare statements. Actual statement equality, proof, and
permitted-axiom checks for those pairs belong to the separate release
Comparator workflow, which validates the inventory before installing its tools.
That workflow downloads the Mathlib cache and builds the library before
Comparator runs, because Comparator's sandbox can read the shared dependency
folder but cannot write to it or reach the network.

Each standalone workspace defaults to its `Challenge` target only. Thus a
plain `lake build` is safe to use while preparing an adversarial Comparator
run: it does not prebuild `Solution.lean`.

## Acceptance

For routine development in a trusted checkout, the standalone driver (also
run by CI) is available. Build the root library first:

```sh
lake exe cache get && lake build
./scripts/build-challenges.sh --trusted-all
```

For a Comparator release run, dispatch `.github/workflows/release-comparator.yml`
on a fresh release-candidate commit. It installs the pinned tools, runs all
seven configurations, and uploads a report artifact. Treat `Solution.lean` as
potentially adversarial. Review and trust the release checkout's `Vocabulary.lean` (and `Vocabulary/`), `Challenge.lean`,
`lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, `config.json`, and
the Comparator toolchain. Then:

1. Run `make challenges-challenge-only` (or run `lake build` in an individual
   workspace). This elaborates only the trusted `Challenge` target and its Mathlib-only vocabulary.
2. Invoke Comparator in its release sandbox with that workspace's
   `config.json`, without first running `lake build Solution` or the trusted
   all-workspace driver.
3. Confirm each theorem depends only on:
   `propext`, `Classical.choice`, and `Quot.sound`.

The ordinary challenge-build driver does not perform statement comparison.

### Recorded acceptance

The release Comparator workflow accepted all seven workspaces on 2026-10-02,
on a standard GitHub-hosted Linux runner, with Lean `v4.35.0-rc3`, Mathlib
`c55e6e7`, AleksandrovDifferentiability `v0.4.0` (built from source),
Comparator `fd5d5bc`, `landrun` `811cfff`, and `lean4export` `66f1fb4`:

| Workspace | Statement comparison and kernel check | Axioms |
|---|---|---|
| `comparison-compact` | PASS | `propext`, `Classical.choice`, `Quot.sound` only |
| `harmonic-dirichlet` | PASS | same |
| `ishii-lemma` | PASS | same |
| `jensen-lemma` | PASS | same |
| `perron-existence` | PASS | same |
| `semijet-testfunction` | PASS | same |
| `uniqueness` | PASS | same |

The GitHub release carries the attestation artifact from running this
workflow on the release commit itself: commit and tree hashes, toolchain and
tool revisions, per-workspace results, and complete logs.
Comparator ran under `landrun` without the additional `systemd-run`
containment that upstream recommends for a full adversarial guarantee, so
these results establish Comparator's checks, not that stronger sandbox claim.

### Scope of each challenge

The comparison result is specialized; uniqueness adds little independent
coverage; Perron checks final assembly under packaged hypotheses, which the harmonic
Dirichlet application discharges for the Laplacian; the Ishii
and Jensen statements are substantive analytic checks; the harmonic
Dirichlet statement is a complete application with Mathlib-only hypotheses
and conclusion, including a ball instance; the smooth
test-function equivalence is a separate foundational check; and the seven
further `comparison-compact` theorems are definition-level sanity checks.
