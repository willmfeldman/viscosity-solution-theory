# Third-party code

This project is released under the Apache License 2.0 (`LICENSE`). A few files contain code
adapted from other Apache-2.0 Lean projects. Each of those files keeps the upstream copyright holder
in its header's copyright line. Each also has a `## Provenance` section in its module docstring
that names the upstream file and commit and says what was changed (Apache-2.0 §4). The upstream
project ships no `NOTICE` file.

| Upstream | License | Upstream copyright | Files here |
|---|---|---|---|
| TauCeti, https://github.com/TauCetiProject/TauCeti (commit 91f66a0514e6523efdccddb9e35fb82c96dd6405) | Apache-2.0 | © 2026 The Tau Ceti contributors | `ViscositySolns/Applications/Laplace/Weyl/LaplacianInvariance.lean`, `ViscositySolns/Applications/Laplace/Weyl/DuBoisReymond.lean`, `ViscositySolns/Applications/Laplace/Weyl/PolarCoord.lean`, `ViscositySolns/Applications/Laplace/Weyl/MeanValue.lean` (ported/adapted) |

All other code is original to this project. Mathlib (Apache-2.0) and
[AleksandrovDifferentiability](https://github.com/willmfeldman/aleksandrov-differentiability)
are used as ordinary library dependencies.
