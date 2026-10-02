module

public import Mathlib

/-!
# Vocabulary: the Dirichlet problem for harmonic functions

Mathlib-only restatement of the library definitions that the statements in
`Challenge.lean` use, under the library's own names. `scripts/challenge-prep.py sync`
copies this file into the generated block of `Challenge.lean`; Comparator checks
each copied declaration against the library by name and value.
-/

@[expose] public section

noncomputable section

open Filter Topology Set
open scoped Gradient Laplacian NNReal

namespace ViscositySolns

/-- Uniform exterior sphere condition: every boundary point `x₀` lies on a
sphere of a fixed radius `R` whose open ball misses `closure U`. -/
def UniformExteriorSphere {d : ℕ} (U : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∃ R > 0, ∀ x₀ ∈ frontier U, ∃ y, dist x₀ y = R ∧ ∀ x ∈ closure U, R ≤ dist x y

end ViscositySolns

end
