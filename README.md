# ViscositySolns

`ViscositySolns` is a Lean 4 formalization of viscosity-solution theory for
second-order degenerate elliptic PDE, following Crandall, Ishii, and Lions'
[*User's guide to viscosity solutions of second order partial differential
equations*](https://doi.org/10.1090/S0273-0979-1992-00266-5). It formalizes
semijets and test functions, the Jensen–Aleksandrov machinery and the
Crandall–Ishii maximum principle used in comparison, and Perron's method for
Dirichlet existence. As an application, it solves the Dirichlet problem for
harmonic functions on bounded `C²` domains. The approximately 59,000 lines of
Lean source are `sorry`-free and introduce no project axioms beyond Lean and
Mathlib's trusted principles.

## Headline theorems

The root module `ViscositySolns` imports the whole library. Its public results
include:

- compact strict comparison:
  `ViscositySolns.strictComparison_of_compact_of_aleksandrov`;
- boundary comparison by the constant-shift argument:
  `ViscositySolns.comparison_of_constantShift_boundary_of_aleksandrov`;
- uniqueness from comparison:
  `ViscositySolns.ViscositySolution.eqOn_of_comparisonConclusions`;
- the quadratic-penalty Crandall–Ishii lemma:
  `ViscositySolns.QuadraticPenaltyIshiiLemmaOn.of_aleksandrov`;
- the localized Jensen contact-set theorem:
  `ViscositySolns.JensenContactSetPositiveMeasureOnClosedBallTheorem.proof`;
- Perron existence for Dirichlet data `g`, with the zero-boundary theorem as
  a special case:
  `ViscositySolns.PerronMethodExistenceTheorem.strictBoundary` and
  `ViscositySolns.PerronMethodExistenceTheorem.strictBoundary_zero`;
- the Dirichlet problem for harmonic functions:
  `ViscositySolns.dirichlet_harmonic_modulus_of_uniformExteriorSphere`.

Perron subsolutions and supersolutions are respectively upper and lower
semicontinuous on the domain together with its boundary. This couples their
boundary inequalities to their interior values. The existence theorem remains
an assembly under comparison and barrier hypotheses; the comparison adapter
in `Existence/Perron/ComparisonAdapter.lean` supplies the comparison premise
from the concrete constant-shift theorem under its structural hypotheses.
`ViscositySolns.dirichletComparisonPrinciple_traceReactionDiffusion` verifies
those hypotheses for `F(x,r,p,X) = r - trace X` on a domain with compact closure.

## Application: harmonic functions

`ViscositySolns/Applications/Laplace/` applies the Perron theorem to the
Laplace equation. Let `U ⊆ ℝᵈ` be a bounded open set with a uniform exterior
sphere condition. For Lipschitz data `g`, there is a classical harmonic
function `h ∈ C(Ū) ∩ C²(U)` with `h = g` on `∂U`. Its boundary modulus
`ϖ(t) = K√t` depends only on `U` and the Lipschitz constant. The statement
uses Mathlib's `EuclideanSpace` and Laplacian.
`uniformExteriorSphere_of_contDiff_levelSet` supplies the exterior sphere
condition for bounded `C²` domains. The proof has four steps:

- a comparison principle for the Laplacian
  (`dirichletComparisonPrinciple_laplaceOperator`);
- exterior-sphere barriers with a Hölder-`1/2` boundary modulus;
- the Perron theorem, which gives a viscosity solution continuous up to the
  boundary;
- classical regularity. A continuous viscosity solution of `Δu = 0` is weakly
  harmonic, by sup-convolution, the Aleksandrov theorem, and Fatou's lemma.
  Weyl's lemma (`ViscositySolns.Analysis.weyl_of_weaklyHarmonicOn`) then makes
  it smooth.

The comparison and Crandall–Ishii results use the public
[AleksandrovDifferentiability](https://github.com/willmfeldman/aleksandrov-differentiability)
formalization for the needed second-differentiability input.

## Building

This project uses the pinned Lean toolchain in `lean-toolchain` and dependency
revisions in `lake-manifest.json`. From a checkout, fetch the Mathlib cache and
build the entire library:

```bash
lake exe cache get
lake build
```

Lake obtains `AleksandrovDifferentiability` from its public Git repository at
a release tag, and downloads that release's prebuilt build archive when one is
available for your platform (otherwise it builds the dependency from source).
The committed manifest locks the resolved revision for reproducible builds.

## Layout

- `ViscositySolns/Foundation.lean`, `Semijets.lean`, and `Solutions.lean`:
  the basic vocabulary of operators, jets, and viscosity solutions.
- `ViscositySolns/Analysis/`: Jensen and Aleksandrov-based analytic results.
- `ViscositySolns/Comparison/`: the Crandall–Ishii lemma, comparison, and
  uniqueness infrastructure.
- `ViscositySolns/Existence/`: Perron envelopes, barriers, bump arguments,
  and existence theorems.
- `ViscositySolns/Stability/` and `TestFunctions/`: stability and
  test-function interfaces.
- `ViscositySolns/Applications/Laplace/`: the harmonic Dirichlet problem,
  including Weyl's lemma (`Weyl/`) and the mean value property.
- `challenges/`: standalone theorem-challenge workspaces and documentation.

## License, citation, and acknowledgements

The project is released under the [Apache License 2.0](LICENSE). Four files
under `Applications/Laplace/Weyl/` are adapted from the Apache-2.0 TauCeti
project; see [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md). If you use
this work, please cite it using [CITATION.cff](CITATION.cff).

The formalization follows the foundational work of Crandall, Ishii, and Lions,
and builds on Lean, Mathlib, and the AleksandrovDifferentiability project.
Authorship and contribution history are recorded in the repository metadata.
