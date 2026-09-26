import Mathlib

/-!
# Challenge: the Dirichlet problem for harmonic functions

Trusted statement surface for the Laplace application of the Perron method.
For a bounded open set `U ⊆ ℝᵈ` and Lipschitz boundary data `g`, there is a
classical harmonic function `h ∈ C(Ū) ∩ C²(U)` with `h = g` on `∂U`. The
boundary modulus of continuity `ϖ` is chosen before `g`, so it depends only on
`U`, the Lipschitz constant `L`, and the bound `M`.

Three forms are stated:

* `challenge_harmonic_dirichlet_c2`: `U` has a `C²` defining function with
  nonvanishing gradient on `∂U`;
* `challenge_harmonic_dirichlet_exteriorSphere`: `U` satisfies a uniform
  exterior sphere condition;
* `challenge_harmonic_dirichlet_ball`: `U` is a Euclidean ball, a concrete
  instance showing that the hypotheses are satisfiable.

Everything is stated with Mathlib notions only: `EuclideanSpace ℝ (Fin d)`,
Mathlib's `gradient` and Laplacian `Δ`, `ContDiffOn`, `LipschitzOnWith`,
`frontier`, and `closure`. The one project definition,
`UniformExteriorSphere`, is restated inline; this file imports `Mathlib` only.
-/

noncomputable section

open Filter Topology Set
open scoped Gradient Laplacian NNReal

namespace ViscositySolns

/-- Uniform exterior sphere condition: every boundary point `x₀` lies on a
sphere of a fixed radius `R` whose open ball misses `closure U`. -/
def UniformExteriorSphere {d : ℕ} (U : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∃ R > 0, ∀ x₀ ∈ frontier U, ∃ y, dist x₀ y = R ∧ ∀ x ∈ closure U, R ≤ dist x y

/--
Challenge: the harmonic Dirichlet problem on a bounded open set with `C²`
boundary, given by a `C²` defining function with nonvanishing gradient on the
boundary, with a boundary modulus uniform over `L`-Lipschitz data bounded by `M`.
-/
theorem challenge_harmonic_dirichlet_c2 {d : ℕ} {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hC2 : ∃ ρ : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ 2 ρ ∧ U = {x | ρ x < 0} ∧
      ∀ x ∈ frontier U, ∇ ρ x ≠ 0)
    (L : ℝ≥0) (M : ℝ) :
    ∃ ϖ : ℝ → ℝ, Tendsto ϖ (𝓝[≥] 0) (𝓝 0) ∧
      ∀ g : EuclideanSpace ℝ (Fin d) → ℝ, LipschitzOnWith L g (closure U) →
        (∀ x ∈ closure U, |g x| ≤ M) →
        ∃ h : EuclideanSpace ℝ (Fin d) → ℝ, ContinuousOn h (closure U) ∧
          ContDiffOn ℝ 2 h U ∧ (∀ x ∈ U, Δ h x = 0) ∧ (∀ x ∈ frontier U, h x = g x) ∧
          ∀ x₀ ∈ frontier U, ∀ x ∈ closure U, |h x - g x₀| ≤ ϖ ‖x - x₀‖ := by
  sorry

/--
Challenge: the harmonic Dirichlet problem on a bounded open set satisfying a
uniform exterior sphere condition.
-/
theorem challenge_harmonic_dirichlet_exteriorSphere {d : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hext : UniformExteriorSphere U) (L : ℝ≥0) (M : ℝ) :
    ∃ ϖ : ℝ → ℝ, Tendsto ϖ (𝓝[≥] 0) (𝓝 0) ∧
      ∀ g : EuclideanSpace ℝ (Fin d) → ℝ, LipschitzOnWith L g (closure U) →
        (∀ x ∈ closure U, |g x| ≤ M) →
        ∃ h : EuclideanSpace ℝ (Fin d) → ℝ, ContinuousOn h (closure U) ∧
          ContDiffOn ℝ 2 h U ∧ (∀ x ∈ U, Δ h x = 0) ∧ (∀ x ∈ frontier U, h x = g x) ∧
          ∀ x₀ ∈ frontier U, ∀ x ∈ closure U, |h x - g x₀| ≤ ϖ ‖x - x₀‖ := by
  sorry

/--
Challenge: the harmonic Dirichlet problem on a Euclidean ball of positive
radius, for Lipschitz data on the closed ball.
-/
theorem challenge_harmonic_dirichlet_ball {d : ℕ} (c : EuclideanSpace ℝ (Fin d)) {t : ℝ}
    (ht : 0 < t) (L : ℝ≥0) (M : ℝ) :
    ∃ ϖ : ℝ → ℝ, Tendsto ϖ (𝓝[≥] 0) (𝓝 0) ∧
      ∀ g : EuclideanSpace ℝ (Fin d) → ℝ, LipschitzOnWith L g (closure (Metric.ball c t)) →
        (∀ x ∈ closure (Metric.ball c t), |g x| ≤ M) →
        ∃ h : EuclideanSpace ℝ (Fin d) → ℝ, ContinuousOn h (closure (Metric.ball c t)) ∧
          ContDiffOn ℝ 2 h (Metric.ball c t) ∧ (∀ x ∈ Metric.ball c t, Δ h x = 0) ∧
          (∀ x ∈ frontier (Metric.ball c t), h x = g x) ∧
          ∀ x₀ ∈ frontier (Metric.ball c t), ∀ x ∈ closure (Metric.ball c t),
            |h x - g x₀| ≤ ϖ ‖x - x₀‖ := by
  sorry

end ViscositySolns
